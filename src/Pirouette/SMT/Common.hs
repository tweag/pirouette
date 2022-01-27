module Pirouette.SMT.Common where

import Pirouette.Term.Syntax
import qualified Pirouette.SMT.SimpleSMT as SmtLib

-- | Prepare a CVC4 solver with all the debug messages and required theories
-- (in particular for datatypes)
prepareSMT :: IO SmtLib.Solver
prepareSMT =
  do
    l <- SmtLib.newLogger 0
    s <- SmtLib.newSolver "cvc4" ["--lang=smt2"] (Just l)
    -- s <- SmtLib.newSolver "cvc4" ["--lang=smt2"] Nothing
    SmtLib.setLogic s "ALL_SUPPORTED"
    return s

-- | Prefix Pirouette names with "pir" to avoid name clashes with SMT builtins
toSmtName :: Name -> String
toSmtName = ("pir_" <>) . show . pretty

-- | What can be translated to an smtlib statement
class Translatable a where
  translate :: a -> SmtLib.SExpr
