{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module PureSMT (module X, Solve(..)) where

import PureSMT.Process as X
import PureSMT.SExpr as X

-- The api to the SMT solver is simple; all the user has to do is inform us how to (A) initialize
-- the solver with a shared context and (B) solve different problems. The @problems@ is supposed
-- to be a GADT in order to fix the different result type of solving different problems.

class Solve domain where
  type Ctx domain :: *
  type Problem domain :: * -> *
  initSolver :: Ctx domain -> Solver -> IO ()
  solveProblem :: Problem domain result -> Solver -> IO result
