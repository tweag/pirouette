{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module implements a pool of external processes, each running an
-- SMT solver. It is often a good idea to import this module qualified as it
-- will re-export a number of functions from "PureSMT.SExpr" to construct S-expressions
module PureSMT (module X, Solve (..), solve, solveOpts, Options (..)) where

import Control.Concurrent.MVar
import Control.Concurrent.QSem
import Control.Monad
import Data.Default
import Data.Kind
import GHC.Conc (numCapabilities)
import PureSMT.Process as X
import PureSMT.SExpr as X
import System.IO.Unsafe (unsafePerformIO)

-- | This class provides an interface to communicate with an individual
-- SMT solver, while the `solve` function provides access to the pool.
--
-- In order to use the pure 'solve' function, you must provide an instance of 'Solve'
-- for your particular domain. The methods of the 'Solve' class are not meant to
-- be called by the user. To provide an instance of 'Solve', you can use the functions
-- in "PureSMT.Process" and "PureSMT.SExpr" to interact with a 'Solver' in a monadic fashion.
class Solve domain where
  -- | Specifies what is the common domain that is supposed to be shared amongst all calls to
  --  the SMT solver
  type Ctx domain :: Type

  -- | Specifies a GADT for the problems that we can solve for this domain.
  type Problem domain :: Type -> Type

  -- | How to initialize a solver with the given context;
  initSolver :: Ctx domain -> Solver -> IO ()

  -- | Solves a problem, producing an associated result with it
  solveProblem :: Problem domain result -> Solver -> IO result

-- | Set of options used for controlling the behavior of the solver.
data Options = Options
  { -- | Whether to echo the interaction with solver to stdout
    debug :: Bool,
    -- | Whether to force a specific number of workers. If set to 'Nothing', will
    --  rely on 'numCapabilities'.
    numWorkers :: Maybe Int
  }
  deriving (Show)

instance Default Options where
  def =
    Options
      { debug = False,
        numWorkers = Nothing
      }

solve :: forall domain res. Solve domain => Ctx domain -> Problem domain res -> res
solve = solveOpts @domain @res def

-- | Evaluates a 'Problem' with an SMT solver chosen from a global pool of
-- SMT solvers.
--
-- At least one pool is started for each value of @Ctx domain@. Note that
-- multiple pools of SMT solvers might be created for the same value of
-- @Ctx domain@ if @solve@ is called from different modules, or if GHC
-- optimizations fail to apply CSE over calls to solve in the same module.
{-# NOINLINE solveOpts #-}
solveOpts :: forall domain res. Options -> Solve domain => Ctx domain -> Problem domain res -> res
solveOpts opts ctx = unsafePerformIO $ do
  -- we end up with a list of MVars, which we will protect in another MVar.
  allProcs <- initAll @domain opts ctx >>= newMStack

  -- Finally, we return the actual closure, the internals make sure
  -- to use 'withMVar' to not mess up the command/response pairs.
  return $ \problem -> unsafePerformIO $ do
    ms <- popMStack allProcs
    r <- withMVar ms $ \solver -> do
      -- TODO: what happens in an exception? For now, we just loose a solver but we shouldn't
      -- add it to the pool of workers and just retry the problem. In a future implementation
      -- we could try launching it again
      solveProblem @domain problem solver
    pushMStack ms allProcs
    return r

initAll :: forall domain. Options -> Solve domain => Ctx domain -> IO [MVar X.Solver]
initAll opts ctx = replicateM nWorkers $ do
  -- TODO: each init creates its own config but they could be shared
  -- this would be especially useful if the solver options are passed
  -- when creating the configuration instead of inside the initSolver
  -- function
  s <- X.launchSolver (debug opts)
  initSolver @domain ctx s
  newMVar s
  where
    nWorkers :: Int
    nWorkers = maybe numCapabilities ensurePos (numWorkers opts)

    ensurePos :: Int -> Int
    ensurePos n = if n >= 1 then n else error "PureSMT: need a positive, non-zero, amount of workers"

-- Type Async Stacks

-- | An 'MStack a' is an 'MVar' having a list of 'a's,
--  which can be popped off the list and pushed back onto it.
--  Popping off an 'MStack' that has no available 'a's just blocks until one becomes available.
type MStack a =
  -- Invariants:
  -- The qsem has no more resources than the length of the list in the MVar
  -- For every element added to the list in the MVar, one resource
  -- is then added in the qsem (although not atomically).
  (QSem, MVar [a])

newMStack :: [a] -> IO (MStack a)
newMStack xs = (,) <$> newQSem (length xs) <*> newMVar xs

pushMStack :: a -> MStack a -> IO ()
pushMStack a (sem, q) = do
  modifyMVar_ q $ pure . (a :)
  signalQSem sem

popMStack :: MStack a -> IO a
popMStack (sem, q) = do
  waitQSem sem
  modifyMVar q $ \case
    [] -> error "invariant disrespected; MStack should not be empty if QSem gives passage"
    (x : xs) -> pure (xs, x)
