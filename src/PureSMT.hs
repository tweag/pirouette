{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module PureSMT (module X, Solve(..), solve) where

import PureSMT.Process as X
import PureSMT.SExpr as X
import Control.Concurrent.MVar
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad

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

{-# NOINLINE solve #-}
solve :: forall domain res . Solve domain => Ctx domain -> Problem domain res -> res
solve ctx = unsafePerformIO $ do
  -- Launch all our worker processes similar to how we did it in TypedProcess2.hs; but now
  -- we end up with a list of MVars, which we will protect in another MVar.
  allProcs <- launchAll @domain ctx >>= newMStack

  -- Finally, we return the actual closure, the internals make sure
  -- to use 'withMVar' to not mess up the command/response pairs.
  return $ \problem -> unsafePerformIO $ do
    ms <- popMStack allProcs
    r <- withMVar ms $ \solver -> do
      -- TODO: what happens in an exception? For now, we just loose a solver but we shouldn't
      -- add it to the pool of workers and just retry the problem. In a future implementation
      -- we could try launching it again
      -- pid <- unsafeSolverPid solver
      -- print pid
      solveProblem @domain problem solver
    pushMStack ms allProcs
    return r

launchAll :: forall domain . Solve domain => Ctx domain -> IO [MVar X.Solver]
launchAll ctx = replicateM numCapabilities $ do
  s <- X.launchSolverWithFinalizer "cvc4 --lang=smt2 --incremental --fmf-fun" debug0
  initSolver @domain ctx s
  newMVar s
  where
    -- TODO: these constants should become parameters at some point; the solver command too!

    numCapabilities :: Int
    numCapabilities = 3

    debug0 :: Bool
    debug0 = False

-- * Async Locks

type Lock = MVar ()

newLock :: IO Lock
newLock = newMVar ()

withLock :: Lock -> IO a -> IO a
withLock lock act = withMVar lock $ Prelude.const act

-- * Async Queues

-- |A MStack is a MVar that satisfies the invariant that it never contains
-- an empty list; if that's the case then the MVar is empty.
type MStack a = (Lock, MVar [a])

newMStack :: [a] -> IO (MStack a)
newMStack [] = (,) <$> newLock <*> newEmptyMVar
newMStack xs = (,) <$> newLock <*> newMVar xs

-- Weirdly enough... removing the withLock makes it work and multiple solvers correctly
-- pick their tasks

pushMStack :: a -> MStack a -> IO ()
pushMStack a (l, q) = do
  mas <- tryTakeMVar q
  case mas of
    Nothing -> putMVar q [a]
    Just as0 -> putMVar q (a:as0)

popMStack :: MStack a -> IO a
popMStack (l, q) = do
  xss <- takeMVar q
  case xss of
    [] -> error "invariant disrespected; MStack should never be empty"
    [x] -> return x
    (x:xs) -> putMVar q xs >> return x
