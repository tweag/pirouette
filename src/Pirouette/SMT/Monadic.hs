{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.SMT.Monadic
  ( SolverT (..),
    checkSat,
    runSolverT,
    solverPush,
    solverPop,
    declareDatatype,
    declareDatatypes,
    supportedUninterpretedFunction,
    declareRawFun,
    declareVariables,
    declareVariable,
    assert,
    assertNot,
    getUnsatCore,
    getModel,

    -- * Convenient re-exports
    Constraint (..),
    PureSMT.Result (..),
    module Base,
    Branch (..),
  )
where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.Writer
import qualified Data.Map as M
import ListT.Weighted (MonadWeightedList)
import Pirouette.Monad
import Pirouette.SMT.Base as Base
import Pirouette.SMT.Constraints
import Pirouette.SMT.FromTerm
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import qualified PureSMT

-- OLD CODE

-- | Solver monad for a specific solver, passed as a phantom type variable @s@ (refer to 'IsSolver' for more)
--  to know the supported solvers. That's a phantom type variable used only to distinguish
--  solver-specific operations, such as initialization
newtype SolverT m a = SolverT {unSolverT :: ReaderT PureSMT.Solver m a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadReader PureSMT.Solver, MonadIO, MonadFail, MonadWeightedList)

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

-- | Returns @Right ()@ when this datatype can be declared as a SMTLIB datatype
supportedDatatype :: (LanguageSMT lang) => TypeDef lang -> Except String ()
supportedDatatype (Datatype _ typeVariables _ cstrs) =
  void $ runWriterT $ mapM (constructorFromPIR typeVariables) cstrs

-- | Declare a set of datatypes (all at once) in the current solver session.
declareDatatypes ::
  (LanguageSMT lang, MonadIO m) => [(Name, TypeDef lang)] -> ExceptT String (SolverT m) [Name]
declareDatatypes [] =
  -- we need to handle this especially because SMTLIB doesn't like an empty set of types
  pure []
declareDatatypes dts = do
  solver <- ask
  (dts', _) <- runWriterT $
    forM dts $ \(typeName, Datatype _ typeVariables _ cstrs) -> do
      cstrs' <- mapM (constructorFromPIR typeVariables) cstrs
      pure (toSmtName typeName, map (toSmtName . fst) typeVariables, cstrs')
  liftIO $ PureSMT.declareDatatypes solver dts'
  return $ concat [typeName : map fst cstrs | (typeName, Datatype _ _ _ cstrs) <- dts]

-- | Returns whether or not a function @f@ can be declared as an uninterpreted function and,
--  if it can, return the type of its arguments and result.
--  A function can be declared if its type can be translate to SmtLib, an uninterpreted function
--  has no body after all, so no need to worry about it.
supportedUninterpretedFunction ::
  (LanguageSMT lang) => FunDef lang -> Maybe ([PureSMT.SExpr], PureSMT.SExpr)
supportedUninterpretedFunction FunDef {funTy} = toMaybe $ do
  let (args, result) = R.tyFunArgs funTy
  (args', _) <- runWriterT $ mapM translateType args
  (result', _) <- runWriterT $ translateType result
  return (args', result')
  where
    toMaybe = either (const Nothing) Just . runExcept

-- | Declares a function with a given name, type of arguments and type of result.
declareRawFun ::
  (MonadIO m) => Name -> ([PureSMT.SExpr], PureSMT.SExpr) -> SolverT m ()
declareRawFun n (args, res) = do
  solver <- ask
  void $ liftIO $ PureSMT.declareFun solver (toSmtName n) args res

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
