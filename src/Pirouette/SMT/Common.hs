module Pirouette.SMT.Common where

import qualified Pirouette.SMT.SimpleSMT as SmtLib

-- | Prepare a CVC4 solver with all the debug messages
prepareSMT :: IO SmtLib.Solver
prepareSMT =
  do
    l <- SmtLib.newLogger 0
    s <- SmtLib.newSolver "cvc4" ["--lang=smt2"] (Just l)
    SmtLib.setLogic s "ALL_SUPPORTED"
    return s
