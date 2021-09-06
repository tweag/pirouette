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

import qualified PlutusCore as P

import           Control.Monad.State
import qualified Data.List.NonEmpty as NE
import           Data.Maybe (mapMaybe)
import qualified Data.Map as M

-- |Removes all Even-Odd mutually recursive functions from the program.
-- When successfull, sets the 'tord' state field with a list of names indicating the order in which
-- they should be defined so that the dependencies of a term @T@ are defined before @T@.
elimEvenOddMutRec :: (MonadPirouette m) => m ()
elimEvenOddMutRec = gets (mapMaybe (uncurry funOrType) . M.toList . decls)
                >>= sortDeps
                >>= foldM (\res c -> (++ res) <$> elimDepCycles c) []
                >>= \ord -> modify (\st -> st { tord = Just ord })
 where
  funOrType n (DFunction {}) = Just $ R.Arg n
  funOrType n (DTypeDef {})  = Just $ R.TyArg n
  funOrType _ _              = Nothing

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
  elimDepCycles :: (MonadPirouette m) => NE.NonEmpty (R.Arg Name Name) -> m [R.Arg Name Name]
  elimDepCycles (e NE.:| []) = return [e]
  elimDepCycles (e NE.:| es) = pushCtx ("elimDepCycles " ++ show (e:es)) $ go (e:es)
    where
      snoc x xs = xs ++ [x]

      -- Because PlutusIR is not dependently typed, it should not be the case that
      -- terms depends on types or vice versa, hence, we should only have to deal with
      -- dependency classes that involve terms or types exclusively.
      go   [] = return []
      go d@(R.TyArg t : ts) = do
        unless (all R.isTyArg ts) $ throwError' $ PEOther "Mixed dependencies"
        logWarn "MutRec Types: TLA+ will error if BoundedSetOf is needed for any of these types."
        return d
      go d@(R.Arg n : ns) =
        case mapM R.fromArg d of
          Nothing -> throwError' $ PEOther "Mixed dependencies"
          Just as -> map R.Arg <$> solveTermDeps 0 as

      -- In order to break the cycle for a class of mutually dependend terms ds, we'll
      -- try to find a non-recursive term d and expand it in all terms in ds \ {d},
      -- then we repeat this until at most one term remains.
      --
      -- If this can't be done, we throw an error
      solveTermDeps _ []  = return []
      solveTermDeps _ [x] = return [x]
      solveTermDeps ctr nss@(n:ns)
        | ctr == length nss = throwError' $ PEMutRecDeps nss
        | otherwise = do
            isRec <- termIsRecursive n
            if isRec
            then solveTermDeps (ctr + 1) (ns ++ [n])
            else mapM_ (expandDefIn n) ns
              >> snoc n <$> solveTermDeps 0 ns

{-
expandDefs :: (MonadPirouette m) => m ()
expandDefs = pushCtx "expandDefs" $ do
  mord <- gets tord
  case mord of
    Nothing  -> throwError' $ PEOther "No dependency order, please call elimEvenOddMutRec"
    Just ord -> modify $ \st -> st { decls = go (decls st) [] ord }
 where
  go :: Decls Name P.DefaultFun -> [(Name, PrtTerm)] -> [R.Arg Name Name]
     -> Decls Name P.DefaultFun
  go decls toInline ns =
-}
