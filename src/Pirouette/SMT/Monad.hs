{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Pirouette.SMT.Monad where

import Control.Arrow ((***))
import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.Bifunctor (bimap)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Pirouette.Monad
import Pirouette.PlutusIR.ToTerm (PlutusIR)
import Pirouette.SMT.Common
import Pirouette.SMT.Translation
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as R

-- | Solver monad for a specific solver, passed as a phantom type variable @s@ (refer to 'IsSolver' for more)
--  to know the supported solvers. That's a phantom type variable used only to distinguish
--  solver-specific operations, such as initialization
newtype SolverT s m a = SolverT {unSolverT :: ReaderT SmtLib.Solver m a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadReader SmtLib.Solver, MonadIO)

runSolverT :: forall s m a. (MonadIO m, IsSolver s) => SolverT s m a -> m a
runSolverT (SolverT comp) = launchSolver @s >>= runReaderT comp

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
solverPush = ask >>= liftIO . SmtLib.push

-- | Pops the current checkpoint, check 'solverPush' for an example.
solverPop :: (MonadIO m) => SolverT s m ()
solverPop = ask >>= liftIO . SmtLib.pop

-- | Declare a single datatype in the current solver session.
declareDatatype :: (LanguageSMT lang, MonadIO m) => Name -> TypeDef lang Name -> SolverT s m ()
declareDatatype typeName typeDef@(Datatype _ typeVariabes _ constructors) = do
  solver <- ask
  liftIO $
    SmtLib.declareDatatype
      solver
      (toSmtName typeName)
      (map (toSmtName . fst) typeVariabes)
      (constructorFromPIR <$> constructors)

-- | Declare a set of datatypes in the current solver session, in the order specified by
-- the dependency order passed as the second argument. You can generally get its value
-- from a 'PirouetteDepOrder' monad.
declareDatatypes ::
  (LanguageSMT lang, MonadIO m) => M.Map Name (PrtDef lang) -> [R.Arg Name Name] -> SolverT s m ()
declareDatatypes decls orderedNames =
  forM_ typeNames $ \tyname ->
    case M.lookup tyname decls of
      Just (DTypeDef tdef) -> declareDatatype tyname tdef
      _ -> return ()
  where
    typeNames = mapMaybe (R.argElim Just (const Nothing)) orderedNames

-- | Declare (name and type) all the variables of the environment in the SMT
-- solver. This step is required before asserting constraints mentioning any of these variables.
declareVariables :: (LanguageSMT lang, MonadIO m) => M.Map Name (PrtType lang) -> SolverT s m ()
declareVariables = mapM_ (uncurry declareVariable) . M.toList

-- | Declares a single variable in the current solver session.
declareVariable :: (LanguageSMT lang, MonadIO m) => Name -> PrtType lang -> SolverT s m ()
declareVariable varName varTy = do
  solver <- ask
  liftIO $ void $ SmtLib.declare solver (toSmtName varName) (translateType varTy)
