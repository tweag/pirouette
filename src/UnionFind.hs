{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This module implements a persistent union-find data structure. This
-- structure reprensents a map from equivalence classes of keys to values. The
-- equivalence relation is irrelevant. The structure primarily provides two
-- operations:
--
-- - @union@ takes two keys and merges their equivalence classes, returning a
--   new structure. Because both keys might be associated to a value, this
--   operation must also be told how to reconcile both values into one.
--
-- - @find@ takes a key and returns the value associated to the key's
--   equivalence class. In order for the structure to remain efficient, @find@
--   also optimises it for future calls and therefore returns a new structure.

module UnionFind where

import Data.Default (Default, def)
import Data.Function ((&))
import Data.Map (Map)
import qualified Data.Map as Map
import Prettyprinter

data UnionFindCell key value
  = ChildOf key
  | Ancestor value

-- | A persistent union-find data structure.
--
-- Invariants:
--
--   (i) There are no cycles.
--   (ii) Keys under @ChildOf@ are present in the map.
--
-- The points (i) and (ii) imply that, if a key is present in the map, then
-- there is a path made of @ChildOf@ constructors from that key to an @Ancestor@
-- constructor.
--
type UnionFind key value = Map key (UnionFindCell key value)

instance Default (UnionFind key value) where
  def = empty

instance (Pretty key, Pretty value) => Pretty (UnionFind key value) where
  pretty unionFind =
    vsep $ map (uncurry prettyBinding) (Map.toList unionFind)
    where
      prettyBinding key1 (ChildOf key2) = pretty key1 <+> "~~" <+> pretty key2
      prettyBinding key (Ancestor value) = pretty key <+> ":=" <+> pretty value

-- | The empty union-find that does not know of any equivalences or values.
--
empty :: UnionFind key value
empty = Map.empty

-- | @findAncestorAndValue unionFind key@ finds the ancestor and value
-- associated to @key@ in the @unionFind@ structure. It returns a new union-find
-- structure with the same semantics but optimised for future calls, the
-- ancestor for @key@ and the found value, or @Nothing@ if @key@ is not in the
-- structure.
--
-- FIXME: Implement the optimisation for future calls
--
findAncestorAndValue :: Ord key => UnionFind key value -> key -> (UnionFind key value, key, Maybe value)
findAncestorAndValue unionFind key =
  case Map.lookup key unionFind of
    Nothing -> (unionFind, key, Nothing)
    Just (ChildOf key') -> findAncestorAndValue unionFind key' -- will be @Just@
    Just (Ancestor value) -> (unionFind, key, Just value)

-- | @find unionFind key@ is the same as @findAncestorAndValue@ but it does not
-- return the ancestor.
--
find :: Ord key => UnionFind key value -> key -> (UnionFind key value, Maybe value)
find unionFind key =
  let (unionFind', _, maybeValue) = findAncestorAndValue unionFind key in
  (unionFind', maybeValue)

-- | @union insert merge unionFind key1 key2@ merges together the equivalence
-- classes of @key1@ and @key2@ in @unionFind@, thus adding the information that
-- @key1@ and @key2@ are equivalent, and returns an updated union-find
-- structure.
--
-- - If neither @key1@ nor @key2@ exists in @unionFind@, @union@ uses @insert@
--   to know whether to return @Nothing@ or to add a specific value.
--
-- - If either @key1@ or @key2@ exists in @unionFind@ but not the other, the
--   other is added transparently to the existing one's equivalence class.
--
-- - If both @key1@ and @key2@ exist in @unionFind@ in the same equivalence
--   class, nothing changes, except that @unionFind@ might be optimised for
--   future calls.
--
-- - If both @key1@ and @key2@ exist in @unionFind@ in distinct equivalence
--   classes, the function @merge@ is called to reconcile the two values
--   associated to the two equivalence classes. @merge@ receives the value
--   associated to @key1@'s equivalence class as first argument and the value
--   associated to @key2@'s equivalence class as second argument.
--
union :: Ord key =>
  Maybe value ->
  (value -> value -> value) ->
  UnionFind key value ->
  key ->
  key ->
  Maybe (UnionFind key value)
union insert merge unionFind key1 key2 =
  let (unionFind1, ancestor1, maybeValue1) = findAncestorAndValue unionFind  key1 in
  let (unionFind2, ancestor2, maybeValue2) = findAncestorAndValue unionFind1 key2 in
  if ancestor1 == ancestor2 then
    Just unionFind2
  else case (maybeValue1, maybeValue2) of
    (Nothing, Nothing) -> do
      value <- insert
      Just $
        unionFind2
        & Map.insert key1 (ChildOf key2)
        & Map.insert key2 (Ancestor value)
    (Just _, Nothing) -> Just $ Map.insert key2 (ChildOf key1) unionFind2
    (Nothing, Just _) -> Just $ Map.insert key1 (ChildOf key2) unionFind2
    (Just value1, Just value2) ->
      -- FIXME: Implement the optimisation that choses which key should be the
      -- other's child by keeping track of the size of the equivalence classes.
      let value = merge value1 value2 in
      Just $
        unionFind2
        & Map.insert key1 (ChildOf key2)
        & Map.insert key2 (Ancestor value)

