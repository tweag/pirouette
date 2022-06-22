{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module PureSMT (module X, Solve(..), solve) where

import PureSMT.Process as X
import PureSMT.SExpr as X
import Control.Concurrent.MVar
import Control.Concurrent.QSem
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad
import GHC.Conc (numCapabilities)

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
      --pid <- unsafeSolverPid solver
      --print pid
      solveProblem @domain problem solver
    pushMStack ms allProcs
    return r

launchAll :: forall domain . Solve domain => Ctx domain -> IO [MVar X.Solver]
launchAll ctx = replicateM numCapabilities $ do
  s <- X.launchSolverWithFinalizer "cvc4 --lang=smt2 --incremental --fmf-fun" debug0
  initSolver @domain ctx s
  newMVar s
  where
    debug0 :: Bool
    debug0 = False

-- * Async Stacks

-- |An 'MStack a' is an 'MVar' having a list of 'a's,
-- which can be popped off the list and pushed back onto it.
-- Popping off an 'MStack' that has no available 'a's just blocks until one becomes available.
type MStack a = (QSem, MVar [a])

newMStack :: [a] -> IO (MStack a)
newMStack xs = (,) <$> newQSem (length xs) <*> newMVar xs

pushMStack :: a -> MStack a -> IO ()
pushMStack a (sem, q) = do
  modifyMVar_ q $ pure . (a :)
  signalQSem sem

popMStack :: MStack a -> IO a
popMStack (sem, q) = do
  waitQSem sem
  modifyMVar q $ \case []     -> error "invariant disrespected; MStack should not be empty if QSem gives passage"
                       (x:xs) -> pure (xs, x)
