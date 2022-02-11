{-# LANGUAGE FlexibleContexts #-}
module Pirouette.SMT where

import Control.Monad.IO.Class
import Pirouette.Monad
import Pirouette.SMT.Common
import Pirouette.SMT.Constraints
import Pirouette.SMT.Datatypes
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.PlutusIR.ToTerm (PlutusIR)

-- | Check satisfiability of a constraint characterizing a symbolic execution
-- path. Note that
smtCheckPathConstraint ::
  (MonadIO m, LanguageSMT lang, ToSMT meta, PirouetteDepOrder lang m) =>
  Env lang -> Constraint lang meta -> m SmtLib.Result
smtCheckPathConstraint env constraint = do
  solver <- prepareSMT
  decls <- prtAllDefs
  dependencyOrder <- prtDependencyOrder
  declareDatatypes solver decls dependencyOrder
  declareVariables solver env
  assertConstraint solver env constraint
  liftIO $ SmtLib.check solver
