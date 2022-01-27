module Pirouette.SMT where

import Pirouette.SMT.Common
import Pirouette.SMT.Datatypes
import Pirouette.SMT.Constraints
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Monad
import Control.Monad.IO.Class

smtCheckPathConstraint :: (MonadIO m, PirouetteDepOrder m) => Env -> Constraint -> m SmtLib.Result
smtCheckPathConstraint env constraint = do
  solver <- liftIO prepareSMT
  decls <- prtAllDefs
  dependencyOrder <- prtDependencyOrder
  liftIO $ declareDatatypes solver decls dependencyOrder
  liftIO $ declareVariables solver env
  liftIO $ assertConstraint solver env constraint
  liftIO $ SmtLib.check solver
