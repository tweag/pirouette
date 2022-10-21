{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UnionFind.Dummy where

import qualified Data.List as List
import Test.QuickCheck ( Arbitrary, arbitrary )
import UnionFind.Monad ( insert, union, WithUnionFind )

-- | Binding in a dummy union-find structure: this is just the pair of a list of
-- keys (with uniqueness) and a possible value.
type DummyUnionFindBinding key value = ([key], Maybe value)

-- | Dummy union-find structure: a list of binding such that there exists no
-- intersection between the left-hand sides of the bindings.
type DummyUnionFind key value = [DummyUnionFindBinding key value]

-- | @extractBinding key duf@ finds the binding to which @key@ belongs in @duf@,
-- or @Nothing@ if there is no such binding. It also returns a dummy union-find
-- structure from which the binding has been removed.
extractBinding ::
  Eq key =>
  key ->
  DummyUnionFind key value ->
  (Maybe (DummyUnionFindBinding key value), DummyUnionFind key value)
extractBinding key = go []
  where
    go prevBindings [] = (Nothing, prevBindings)
    go prevBindings (binding : nextBindings)
      | key `elem` fst binding = (Just binding, prevBindings ++ nextBindings)
      | otherwise = go (binding : prevBindings) nextBindings

-- | Insertion of a binding in a dummy union-find structure.
insert ::
  Eq key =>
  (value -> value -> value) ->
  key ->
  value ->
  DummyUnionFind key value ->
  DummyUnionFind key value
insert merge key value duf =
  let (mBinding, duf') = extractBinding key duf
   in case mBinding of
    Nothing -> ([key], Just value) : duf'
    Just (keys, maybeValue) ->
      let newValue = maybe value (merge value) maybeValue
       in (keys, Just newValue) : duf'

-- | Union of equivalence classes in a dummy union-find structure.
union ::
  Eq key =>
  (value -> value -> value) ->
  key ->
  key ->
  DummyUnionFind key value ->
  DummyUnionFind key value
union merge key1 key2 duf =
  let (mBinding1, duf1) = extractBinding key1 duf
      -- NOTE: if @key1@ and @key@ belong to the same equivalence class in
      -- @duf@, then @mBinding2@ is @Nothing@. The cases take that into account.
      (mBinding2, duf2) = extractBinding key2 duf1
   in case (mBinding1, mBinding2) of
        (Nothing, Nothing) ->
          ([key1] `List.union` [key2], Nothing) : duf2
        (Nothing, Just (keys2, mValue2)) ->
          (keys2 `List.union` [key1], mValue2) : duf2
        (Just (keys1, mValue1), Nothing) ->
          (keys1 `List.union` [key2], mValue1) : duf2
        (Just (keys1, mValue1), Just (keys2, mValue2)) ->
          (keys1 `List.union` keys2, merge <$> mValue1 <*> mValue2) : duf2