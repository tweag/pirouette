{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.TransitiveDeps where

import Control.Arrow (first, second)
import Control.Monad.State
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R

-- | Reads in all function and type definitions and computes an order in which definitions
--  should be declared so that if @f@ depends on @g@, @g@ is declared before @f@ is defined.
--
--  Returns a list of (non-empty) lists where the inner lists represent mutually recursive
--  definitions.
sortAllDeps :: (PirouetteReadDefs lang m) => m [NonEmpty (R.Arg Name Name)]
sortAllDeps = do
  allDefs <- prtAllDefs
  let funOrTyDefs = mapMaybe (uncurry funOrType) . M.toList $ allDefs
  evalStateT (sortDepsCached funOrTyDefs) (TranDepsCache M.empty)
  where
    funOrType (_, n) DFunction {} = Just $ R.TermArg n
    funOrType (_, n) DTypeDef {} = Just $ R.TyArg n
    funOrType _ _ = Nothing

-- | Returns the type and term-level transitive dependencies associated with a name.
--  This is an expensive computation that you might want to memoize; therefore, check
--  'transitiveDepsOfCached' also.
transitiveDepsOf :: (PirouetteReadDefs lang m) => Name -> m (S.Set (R.Arg Name Name))
transitiveDepsOf n = evalStateT (transitiveDepsOfCached n) (TranDepsCache M.empty)

-- ** Cached Variants

newtype TranDepsCache = TranDepsCache {trDepsOf :: M.Map Name (S.Set (R.Arg Name Name))}

-- | Given a list of names, sort them according to their dependencies.
sortDepsCached ::
  (PirouetteReadDefs lang m, MonadState TranDepsCache m) =>
  [R.Arg Name Name] ->
  m [NonEmpty (R.Arg Name Name)]
sortDepsCached = equivClassesM (\x d -> S.member x <$> transitiveDepsOfCached (R.argElim id id d))

transitiveDepsOfCached ::
  forall lang m.
  (PirouetteReadDefs lang m, MonadState TranDepsCache m) =>
  Name ->
  m (S.Set (R.Arg Name Name))
transitiveDepsOfCached = go S.empty
  where
    go :: S.Set Name -> Name -> m (S.Set (R.Arg Name Name))
    go stack n0 = do
      mr <- gets (M.lookup n0 . trDepsOf)
      case mr of
        Just ds -> return ds
        Nothing -> do
          r <- computeDeps stack n0
          modify (TranDepsCache . M.insert n0 r . trDepsOf)
          return r

    computeDeps stack n0
      | n0 `S.member` stack = return S.empty
      | otherwise = do
        deps0 <- directDepsOf n0
        let stack' = S.insert n0 stack
        let deps1 = S.map (R.argElim id id) deps0
        S.unions . (deps0 :) <$> mapM (go stack') (S.toList deps1)

-- *** Utility Functions

partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM _ [] = return ([], [])
partitionM f (x : xs) = f x >>= (<$> partitionM f xs) . ite (first (x :)) (second (x :))
  where
    ite t _ True = t
    ite _ e False = e

-- | Given a preorder relation @depM@, 'equivClassesM' computes
--  the equivalence classes of @depM@, on @xs@ such that if
--
--  > equivClassesM depOn xs == [r0, ..., rN]
--
--  Then each @m, n@ in @ri@ for some @i@ is mutually dependent @depOn m n && depOn n m@
--  and if there exists @m@ in @ri@ and @n@ in @rj@, then @i >= j@ iff @depOn m n@.
equivClassesM :: (Monad m) => (a -> a -> m Bool) -> [a] -> m [NonEmpty a]
equivClassesM _depM [] = return []
equivClassesM depM (d : ds) = do
  -- we start by splitting the dependencies of d from the rest,
  (depsOfD, aft) <- partitionM (depM d) ds
  -- Now, out the dependencies of d, we split off those that depend on d itself.
  (eq, bef) <- partitionM (`depM` d) depsOfD
  bef' <- equivClassesM depM bef
  aft' <- equivClassesM depM aft
  return $ bef' ++ ([d :| eq] ++ aft')

-- Non-monadic version of 'equivClassesM'; useful for testing
-- equivClasses :: (a -> a -> Bool) -> [a] -> [NonEmpty a]
-- equivClasses leq = runIdentity . equivClassesM (\a -> return . leq a)
