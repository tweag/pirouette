{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- | This is Pirouette's SMT solver interface; you probably won't need to import
--  anything under the @SMT/@ folder explicitely unless you're trying to do some
--  very specific things or declaring a language. In which case, you probably
--  want only "Pirouette.SMT.Base" and "Pirouette.SMT.PureSMT" to bring get the necessary
--  classes and definitions in scope. Check "Language.Pirouette.PlutusIR.SMT" for an example.
module Pirouette.SMT
  ( SolverT (..),
    checkSat,
    runSolverT,
    solverPush,
    solverPop,
    declareDatatype,
    declareDatatypes,
    supportedUninterpretedFunction,
    declareRawFun,
    declareUninterpretedFunction,
    declareUninterpretedFunctions,
    declareAsManyUninterpretedFunctionsAsPossible,
    declareVariables,
    declareVariable,
    assert,
    assertNot,
    getUnsatCore,
    getModel,

    -- * New interface
    Solve (..),

    -- * Convenient re-exports
    Constraint (..),
    AtomicConstraint (..),
    PureSMT.Result (..),
    module Base,
    Branch (..),
    LanguageSMTBranches (..),
  )
where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.Writer
import qualified Data.Map as M
import Data.Maybe (catMaybes, mapMaybe)
import ListT.Weighted (MonadWeightedList)
import Pirouette.Monad
import Pirouette.Monad.Logger
import Pirouette.SMT.Base as Base
import Pirouette.SMT.Constraints
import qualified PureSMT
import Pirouette.SMT.Translation
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import System.IO.Unsafe (unsafePerformIO)

-- The api to the SMT solver is simple; all the user has to do is inform us how to (A) initialize
-- the solver with a shared context and (B) solve different problems. The @problems@ is supposed
-- to be a GADT in order to fix the different result type of solving different problems.

class Solve lang where
  type Ctx lang :: *
  type Problem lang :: * -> *
  initSolver :: Ctx lang -> PureSMT.Solver -> IO ()
  solveProblem :: Problem lang probRes -> PureSMT.Solver -> IO probRes

-- OLD CODE

-- | Solver monad for a specific solver, passed as a phantom type variable @s@ (refer to 'IsSolver' for more)
--  to know the supported solvers. That's a phantom type variable used only to distinguish
--  solver-specific operations, such as initialization
newtype SolverT m a = SolverT {unSolverT :: ReaderT PureSMT.Solver m a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadReader PureSMT.Solver, MonadIO, MonadLogger, MonadFail, MonadWeightedList)

instance MonadTrans SolverT where
  lift = SolverT . lift

deriving instance MonadState s m => MonadState s (SolverT m)

deriving instance MonadError e m => MonadError e (SolverT m)

deriving instance Alternative m => Alternative (SolverT m)

deriving instance PirouetteReadDefs lang m => PirouetteReadDefs lang (SolverT m)

-- | Runs a computation that requires a session with a solver. The first parameter is
-- an action that launches a solver. Check 'cvc4_ALL_SUPPORTED' for an example.
runSolverT :: forall m a. (MonadIO m) => IO PureSMT.Solver -> SolverT m a -> m a
runSolverT s (SolverT comp) = liftIO s >>= runReaderT comp

-- | Returns 'Sat', 'Unsat' or 'Unknown' for the current solver session.
checkSat :: (MonadIO m) => SolverT m PureSMT.Result
checkSat = do
  solver <- ask
  liftIO $ PureSMT.check solver

-- | Pushes the solver context, creating a checkpoint. This is useful if you plan to execute
--  many queries that share definitions. A typical use pattern would be:
--
--  > declareDatatypes ...
--  > forM_ varsAndExpr $ \(vars, expr) -> do
--  >   solverPush
--  >   declareVariables vars
--  >   assert expr
--  >   r <- checkSat
--  >   solverPop
--  >   return r
solverPush :: (MonadIO m) => SolverT m ()
solverPush = do
  solver <- ask
  liftIO $ PureSMT.push solver

-- | Pops the current checkpoint, check 'solverPush' for an example.
solverPop :: (MonadIO m) => SolverT m ()
solverPop = do
  solver <- ask
  liftIO $ PureSMT.pop solver

-- | Declare a single datatype in the current solver session.
declareDatatype :: (LanguageSMT lang, MonadIO m) => Name -> TypeDef lang -> ExceptT String (SolverT m) [Name]
declareDatatype typeName (Datatype _ typeVariables _ cstrs) = do
  solver <- ask
  (constr', _) <- runWriterT $ mapM (constructorFromPIR typeVariables) cstrs
  liftIO $ do
    PureSMT.declareDatatype
      solver
      (toSmtName typeName)
      (map (toSmtName . fst) typeVariables)
      constr'
  return $ typeName : map fst cstrs

-- | Declare a set of datatypes in the current solver session, in the order specified by
-- the list of definitions. For info on sorting definitions, check the 'PirouetteDepOrder' class.
declareDatatypes ::
  (LanguageSMT lang, MonadIO m) => [(Name, TypeDef lang)] -> ExceptT String (SolverT m) [Name]
declareDatatypes = fmap concat . mapM (uncurry declareDatatype)

-- |If a function can be declared as an uninterpreted function, returns
-- the type of its arguments and the type of its result.
supportedUninterpretedFunction ::
  (LanguageSMT lang) => FunDef lang -> Maybe ([PureSMT.SExpr], PureSMT.SExpr)
supportedUninterpretedFunction FunDef {funTy} = toMaybe $ do
  let (args, result) = R.tyFunArgs funTy
  (args', _) <- runWriterT $ mapM translateType args
  (result', _) <- runWriterT $ translateType result
  return (args', result')
 where
   toMaybe = either (const Nothing) Just . runExcept

declareRawFun ::
  (MonadIO m) => Name -> ([PureSMT.SExpr], PureSMT.SExpr) -> SolverT m ()
declareRawFun n (args, res) = do
  solver <- ask
  void $ liftIO $ PureSMT.declareFun solver (toSmtName n) args res

-- | Declare a single function signature as uninterpreted
-- in the current solver session.
declareUninterpretedFunction ::
  (LanguageSMT lang, MonadIO m) => Name -> FunDef lang -> ExceptT String (SolverT m) Name
declareUninterpretedFunction fnName FunDef {funTy} = do
  solver <- ask
  let (args, result) = R.tyFunArgs funTy
  (args', _) <- runWriterT $ mapM translateType args
  (result', _) <- runWriterT $ translateType result
  _ <- liftIO $ PureSMT.declareFun solver (toSmtName fnName) args' result'
  return fnName

declareUninterpretedFunctions ::
  (LanguageSMT lang, MonadIO m) =>
  M.Map Name (Definition lang) ->
  [R.Arg Name Name] ->
  ExceptT String (SolverT m) [Name]
declareUninterpretedFunctions decls orderedNames = do
  let fnNames = mapMaybe (R.argElim (const Nothing) Just) orderedNames
  forMaybeM fnNames $ \fnName ->
    case M.lookup fnName decls of
      Just (DFunDef fdef) -> Just <$> declareUninterpretedFunction fnName fdef
      _ -> return Nothing

declareAsManyUninterpretedFunctionsAsPossible ::
  (LanguageSMT lang, MonadIO m) =>
  [(Name, FunDef lang)] ->
  ExceptT String (SolverT m) [Name]
declareAsManyUninterpretedFunctionsAsPossible ds = do
  forMaybeM ds $ \(fnName, fnDef) ->
    (Just <$> declareUninterpretedFunction fnName fnDef)
      `catchError` (\_ -> return Nothing)

-- | Declare (name and type) all the variables of the environment in the SMT
-- solver. This step is required before asserting constraints mentioning any of these variables.
declareVariables :: (LanguageSMT lang, MonadIO m) => M.Map Name (Type lang) -> ExceptT String (SolverT m) ()
declareVariables = mapM_ (uncurry declareVariable) . M.toList

-- | Declares a single variable in the current solver session.
declareVariable :: (LanguageSMT lang, MonadIO m) => Name -> Type lang -> ExceptT String (SolverT m) ()
declareVariable varName varTy = do
  solver <- ask
  (tySExpr, _) <- runWriterT $ translateType varTy
  liftIO $ void (PureSMT.declare solver (toSmtName varName) tySExpr)

-- | Asserts a constraint; check 'Constraint' for more information
-- | The functions 'assert' and 'assertNot' output a boolean,
-- stating if the constraint was fully passed to the SMT solver,
-- or if a part was lost during the translation process.
assert ::
  (MonadIO m) =>
  PureSMT.SExpr ->
  SolverT m ()
assert expr =
  SolverT $
    ReaderT $ \solver -> do
      liftIO $ PureSMT.assert solver expr

assertNot ::
  (MonadIO m) =>
  PureSMT.SExpr ->
  SolverT m ()
assertNot expr =
  SolverT $
    ReaderT $ \solver -> do
      -- liftIO $ putStrLn $ "asserting not " ++ show expr
      liftIO $ PureSMT.assert solver (PureSMT.not expr)

getUnsatCore ::
  (MonadIO m) =>
  SolverT m [String]
getUnsatCore = SolverT $
  ReaderT $ \solver ->
    liftIO $ PureSMT.getUnsatCore solver

getModel ::
  (MonadIO m) =>
  [Name] ->
  SolverT m [(PureSMT.SExpr, PureSMT.Value)]
getModel names = SolverT $
  ReaderT $ \solver -> do
    let exprs = map (PureSMT.symbol . toSmtName) names
    liftIO $ PureSMT.getExprs solver exprs

-- Utility functions

concatForM :: (Traversable t, Monad f) => t a -> (a -> f [b]) -> f [b]
concatForM xs action = concat <$> forM xs action

forMaybeM :: (Monad f) => [a] -> (a -> f (Maybe b)) -> f [b]
forMaybeM xs action = catMaybes <$> forM xs action
