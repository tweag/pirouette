{-# LANGUAGE AllowAmbiguousTypes #-}
module Pirouette.SMT.Common where

import Control.Monad.IO.Class
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax

-- | Prepare a CVC4 solver with all the debug messages and required theories
-- (in particular for datatypes)
prepareSMT :: MonadIO m => m SmtLib.Solver
prepareSMT =
  do
    -- This generates a "Solver" which logs every interaction it has.
    -- To suppress this logging, replace the 2 next lines by
    -- s <- liiftIO $ SmtLib.newSolver "cvc4" ["--lang=smt2"] Nothing
    l <- liftIO $ SmtLib.newLogger 0
    s <- liftIO $ SmtLib.newSolver "cvc4" ["--lang=smt2"] (Just l)
    liftIO $ SmtLib.setLogic s "ALL_SUPPORTED"
    return s

-- | Prefix Pirouette names with "pir" to avoid name clashes with SMT builtins
toSmtName :: Name -> String
toSmtName = ("pir_" <>) . show . pretty

-- | Captures the languages that can be translated to SMTLIB; namelly,
-- we need to be able to translate each individual base syntactical category.
--
-- This class is defined with @-XAllowAmbiguousTypes@ and therefore
-- should be used with @-XTypeApplications@.
class (LanguageDef lang) => LanguageSMT lang where
  translateBuiltinType :: BuiltinTypes lang -> SmtLib.SExpr
  translateBuiltinTerm :: BuiltinTerms lang -> SmtLib.SExpr
  translateConstant :: Constants lang -> SmtLib.SExpr
