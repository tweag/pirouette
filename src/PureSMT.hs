{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module PureSMT (module X, Solve(..)) where

import PureSMT.Process as X
import PureSMT.SExpr as X

-- |In order to use the pure 'solve' function, you must provide an instance of 'Solve'
-- for your particular domain. The methods of the 'Solve' class are not meant to
-- be called by the user. To provide an instance of 'Solve', you can use the functions
-- in "PureSMT.Process" and "PureSMT.SExpr" to interact with a 'Solver' in a monadic fashion.
class Solve domain where
  -- |Specifies what is the common domain that is supposed to be shared amongst all calls to
  -- the SMT solver
  type Ctx domain :: *
  -- |Specifies a GADT for the problems that we can solve for this domain.
  type Problem domain :: * -> *

  -- |How to initialize a solver with the given context;
  initSolver :: Ctx domain -> Solver -> IO ()

  -- |Solves a problem, producing an associated result with it
  solveProblem :: Problem domain result -> Solver -> IO result
