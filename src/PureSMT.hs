{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TypeApplications #-}
module PureSMT (module X, Solve(..), solve) where

import PureSMT.Process (Solver)
import qualified PureSMT.Process as X
import PureSMT.SExpr as X
import Control.Concurrent
import Control.Monad
import System.IO.Unsafe (unsafePerformIO)

-- The api to the SMT solver is simple; all the user has to do is inform us how to (A) initialize
-- the solver with a shared context and (B) solve different problems. The @problems@ is supposed
-- to be a GADT in order to fix the different result type of solving different problems.

class Solve domain where
  type Ctx domain :: *
  type Problem domain :: * -> *
  initSolver :: Ctx domain -> Solver -> IO ()
  solveProblem :: Problem domain result -> Solver -> IO result

{-# NOINLINE solve #-}
solve :: forall domain res . Solve domain => Ctx domain -> Problem domain res -> res
solve ctx = unsafePerformIO $ do
  -- Launch all our worker processes similar to how we did it in TypedProcess2.hs; but now
  -- we end up with a list of MVars, which we will protect in another MVar.
  allProcs <- launchAll @domain ctx >>= newMStack

  -- Finally, we return the actual length function, which is ran in a 'catch'
  -- block to make sure we get to respond in case of a bad exception and
  -- the internals make sure to use 'withMVar' to not mess up the command/response
  -- pairs.
  return $ \problem -> unsafePerformIO $ do
    ms <- pop allProcs
    r <- withMVar ms $ \solver -> do
      solveProblem @domain problem solver
    push ms allProcs
    return r

launchAll :: forall domain . Solve domain => Ctx domain -> IO [MVar X.Solver]
launchAll ctx = replicateM nUMWORKERS $ do
  s <- X.launchSolverWithFinalizer "cvc4" dEBUG
  initSolver @domain ctx s
  newMVar s

nUMWORKERS :: Int
nUMWORKERS = 4

dEBUG :: Bool
dEBUG = False

-- * Async Queues

-- |A MStack is a MVar that satisfies the invariant that it never contains
-- an empty list; if that's the case then the MVar is empty.
type MStack a = MVar [a]

newMStack :: [a] -> IO (MStack a)
newMStack [] = newEmptyMVar
newMStack xs = newMVar xs

push :: a -> MStack a -> IO ()
push a q = do
  mas <- tryTakeMVar q
  case mas of
    Nothing -> putMVar q [a]
    Just as0 -> putMVar q (a:as0)

pop :: MStack a -> IO a
pop q = do
  xss <- takeMVar q
  case xss of
    [] -> error "invariant disrespected; MStack should never be empty"
    [x] -> return x
    (x:xs) -> putMVar q xs >> return x
