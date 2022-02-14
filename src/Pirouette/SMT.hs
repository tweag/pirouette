{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This is Pirouette's SMT solver interface; you probably won't need to import
--  anything under the @SMT/@ folder explicitely unless you're trying to do some
--  very specific things or declaring a language. In which case, you probably
--  want only "Pirouette.SMT.Base" and "Pirouette.SMT.SimpleSMT" to bring get the necessary
--  classes and definitions in scope. Check "Pirouette.PlutusIR.SMT" for an example.
module Pirouette.SMT
  ( SolverT (..),
    checkSat,
    runSolverT,
    solverPush,
    solverPop,
    declareDatatype,
    declareDatatypes,
    declareVariables,
    declareVariable,
    assert,

    -- * Convenient re-exports
    Constraint(..),
    SimpleSMT.Result (..),
    module Base,
  )
where

import Control.Arrow ((***))
import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.Bifunctor (bimap)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Pirouette.Monad
import Pirouette.PlutusIR.ToTerm (PlutusIR)
import Pirouette.SMT.Base as Base
import Pirouette.SMT.Constraints
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import Pirouette.SMT.Translation
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as R
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Applicative

-- | Solver monad for a specific solver, passed as a phantom type variable @s@ (refer to 'IsSolver' for more)
--  to know the supported solvers. That's a phantom type variable used only to distinguish
--  solver-specific operations, such as initialization
newtype SolverT s m a = SolverT {unSolverT :: ReaderT SimpleSMT.Solver m a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadReader SimpleSMT.Solver, MonadIO)

instance MonadTrans (SolverT s) where
  lift = SolverT . lift

deriving instance MonadState s m => MonadState s (SolverT sol m)
deriving instance MonadError e m => MonadError e (SolverT sol m)
deriving instance Alternative m => Alternative (SolverT sol m)

-- | Runs a computation that requires a session with a solver. You can specify
--  which solver you want through a type application:
--
--  > runSolverT @CVC4 ...
runSolverT :: forall s m a. (MonadIO m, IsSolver s) => SolverT s m a -> m a
runSolverT (SolverT comp) = launchSolver @s >>= runReaderT comp

-- | Returns 'Sat', 'Unsat' or 'Unknown' for the current solver session.
checkSat :: (MonadIO m) => SolverT s m SimpleSMT.Result
checkSat = ask >>= liftIO . SimpleSMT.check

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
solverPush :: (MonadIO m) => SolverT s m ()
solverPush = ask >>= liftIO . SimpleSMT.push

-- | Pops the current checkpoint, check 'solverPush' for an example.
solverPop :: (MonadIO m) => SolverT s m ()
solverPop = ask >>= liftIO . SimpleSMT.pop

-- | Declare a single datatype in the current solver session.
declareDatatype :: (LanguageSMT lang, MonadFail m, MonadIO m) => Name -> TypeDef lang Name -> SolverT s m ()
declareDatatype typeName typeDef@(Datatype _ typeVariabes _ constructors) = do
  solver <- ask
  liftIO $ do
    constr' <- mapM constructorFromPIR constructors
    SimpleSMT.declareDatatype
      solver
      (toSmtName typeName)
      (map (toSmtName . fst) typeVariabes)
      constr'

-- | Declare a set of datatypes in the current solver session, in the order specified by
-- the dependency order passed as the second argument. You can generally get its value
-- from a 'PirouetteDepOrder' monad.
declareDatatypes ::
  (LanguageSMT lang, MonadIO m, MonadFail m) => M.Map Name (PrtDef lang) -> [R.Arg Name Name] -> SolverT s m ()
declareDatatypes decls orderedNames =
  forM_ typeNames $ \tyname ->
    case M.lookup tyname decls of
      Just (DTypeDef tdef) -> declareDatatype tyname tdef
      _ -> return ()
  where
    typeNames = mapMaybe (R.argElim Just (const Nothing)) orderedNames

-- | Declare (name and type) all the variables of the environment in the SMT
-- solver. This step is required before asserting constraints mentioning any of these variables.
declareVariables :: (LanguageSMT lang, MonadIO m, MonadFail m) => M.Map Name (PrtType lang) -> SolverT s m ()
declareVariables = mapM_ (uncurry declareVariable) . M.toList

-- | Declares a single variable in the current solver session.
declareVariable :: (LanguageSMT lang, MonadIO m, MonadFail m) => Name -> PrtType lang -> SolverT s m ()
declareVariable varName varTy = do
  solver <- ask
  liftIO $ translateType varTy >>= void . SimpleSMT.declare solver (toSmtName varName)

-- | Asserts a constraint; check 'Constraint' for more information
assert ::
  (LanguageSMT lang, ToSMT meta, MonadIO m, MonadFail m) =>
  M.Map Name (PrtType lang) ->
  Constraint lang meta ->
  SolverT s m ()
assert gamma c = SolverT $ ReaderT $ \solver -> assertConstraintRaw solver gamma c
