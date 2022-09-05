{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.ElimEvenOddMutRec where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Term.TransitiveDeps
import Pirouette.Transformations.Inline

-- | Removes all Even-Odd mutually recursive functions from the program.
-- When successful, it also computes the correct order of definitions according to dependencies between them,
-- storing it in the 'prtDepOrder' field in the resulting 'PrtOrderedDefs'.
elimEvenOddMutRec :: forall lang. (LanguageBuiltins lang) => PrtUnorderedDefs lang -> PrtOrderedDefs lang
elimEvenOddMutRec udefs = runIdentity $ do
  ordWithCycles <- runReaderT sortAllDeps udefs
  (ord, udefs') <- runStateT (foldM (\res c -> (++ res) <$> elimDepCycles c) [] ordWithCycles) udefs
  return $ prtOrderedDefs udefs' ord
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
    elimDepCycles ::
      (LanguageBuiltins lang, Monad m) =>
      NonEmpty (SystF.Arg Name Name) ->
      StateT (PrtUnorderedDefs lang) m [SystF.Arg Name Name]
    elimDepCycles (e :| []) = return [e]
    elimDepCycles (e :| es) = go (e : es)
      where
        snoc x xs = xs ++ [x]

        -- Because PlutusIR is not dependently typed, it should not be the case that
        -- terms depends on types or vice versa, hence, we should only have to deal with
        -- dependency classes that involve terms or types exclusively.
        go [] = return []
        go d@(SystF.TyArg _t : ts) = do
          unless (all SystF.isTyArg ts) $ prtError $ PEOther "Mixed dependencies"
          return d
        go d@(SystF.TermArg _n : _ns) =
          case mapM SystF.fromArg d of
            Nothing -> prtError $ PEOther "Mixed dependencies"
            Just as -> map SystF.TermArg <$> solveTermDeps 0 as

        -- In order to break the cycle for a class of mutually dependend terms ds, we'll
        -- try to find a non-recursive term d and expand it in all terms in ds \ {d},
        -- then we repeat this until at most one term remains.
        --
        -- If this can't be done, we throw an error
        solveTermDeps _ [] = return []
        solveTermDeps _ [x] = return [x]
        solveTermDeps ctr nss@(n : ns)
          | ctr == length nss = prtError $ PEMutRecDeps nss
          | otherwise = do
            isRec <- termIsRecursive n
            if isRec
              then solveTermDeps (ctr + 1) (ns ++ [n])
              else
                mapM_ (expandDefInSt n) ns
                  >> snoc n <$> solveTermDeps 0 ns

        expandDefInSt :: (Monad m) => Name -> Name -> StateT (PrtUnorderedDefs lang) m ()
        expandDefInSt n m = do
          defn <- prtTermDefOf n
          modify (\st -> st {prtUODecls = fst $ expandDefsIn (Map.singleton n defn) (prtUODecls st) m})
