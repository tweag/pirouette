-- |Implements whole-program transformations. If you're looking
-- for term transformations, check "Pirouette.Term.Transformations"
--
module Pirouette.Transformations where

import           Pirouette.Monad
import           Pirouette.Monad.Logger
import           Pirouette.Monad.Maybe
import           Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax.Subst
import           Pirouette.Term.Transformations

import           Control.Monad.State
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M

-- |Removes all Even-Odd mutually recursive functions from the program.
-- When successfull, returns a list of names indicating the order in which
-- they should be defined so that the dependencies of a term @T@ are defined
-- before @T@.
elimEvenOddMutRec :: (MonadPirouette m) => m [Name]
elimEvenOddMutRec = gets (M.keys . decls)
                >>= sortDeps
                >>= foldM (\res c -> (res ++) <$> elimDepCycles c) []
 where
  -- Attempts to eliminate dependency cycles for a set of mutually recursive definitions.
  -- If successfull, returns a @ns@ containing the order in which the
  -- inputs should be declared. The declarations within the state monad will
  -- have been updated accordingly. Take the following situation:
  --
  -- > f x = op1 (f (x-1)) (g x)
  -- > g x = h x + 2
  -- > h x = f (x - 3)
  --
  -- Calling @elimDepCycles ["f", "g", "h"]@ will return @["f", "h", "g"]@ and
  -- will alter the definitions to:
  --
  -- > f x = op1 (f (x-1)) (f (x - 3) - 2)
  -- > h x = f (x - 3)
  -- > g x = h x + 2
  --
  elimDepCycles :: (MonadPirouette m) => NE.NonEmpty Name -> m [Name]
  elimDepCycles (e NE.:| []) = return [e]
  elimDepCycles (e NE.:| es) = pushCtx ("elimDepCycles " ++ show (e:es)) $ go 0 (e:es)
    where
      snoc x xs = xs ++ [x]

      go _ [] = return []
      go ctr nss@(n:ns)
        | ctr == length ns = throwError' $ PEMutRecDeps ns
        | otherwise = do
            isRec <- termIsRecursive n
            if isRec
            then go (ctr + 1) (ns ++ [n])
            else mapM_ (expandDefIn n) ns
              >> snoc n <$> go 0 ns
