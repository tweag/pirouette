{-# LANGUAGE LambdaCase #-}
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
import Data.Either (partitionEithers)
import Data.Function ((&))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
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
newtype UnionFind key value = UnionFind {
  getMap :: Map key (UnionFindCell key value)
}

instance Default (UnionFind key value) where
  def = empty

instance (Pretty key, Pretty value) => Pretty (UnionFind key value) where
  pretty unionFind =
    vsep $ map (uncurry prettyBinding) (Map.toList $ getMap unionFind)
    where
      prettyBinding key1 (ChildOf key2) = pretty key1 <+> "~~" <+> pretty key2
      prettyBinding key (Ancestor value) = pretty key <+> ":=" <+> pretty value

-- | The empty union-find that does not know of any equivalences or values.
--
empty :: UnionFind key value
empty = UnionFind Map.empty

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
  case Map.lookup key $ getMap unionFind of
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
  else
    let onUnionFind2sMap update = Just $ UnionFind $ update $ getMap $ unionFind2 in
    case (maybeValue1, maybeValue2) of
    (Nothing, Nothing) -> do
      value <- insert
      onUnionFind2sMap $ Map.insert key1 (ChildOf key2)
                       . Map.insert key2 (Ancestor value)
    (Just _, Nothing) ->
      onUnionFind2sMap $ Map.insert key2 (ChildOf key1)
    (Nothing, Just _) ->
      onUnionFind2sMap $ Map.insert key1 (ChildOf key2)
    (Just value1, Just value2) ->
      -- FIXME: Implement the optimisation that choses which key should be the
      -- other's child by keeping track of the size of the equivalence classes.
      onUnionFind2sMap $ Map.insert key1 (ChildOf key2)
                       . Map.insert key2 (Ancestor $ merge value1 value2)

-- | Same as @union@ for trivial cases where one knows for sure that:
--
-- - At least one of the keys is in the structure.
-- - The keys are not in the same equivalence class (or one is absent).
--
trivialUnion :: Ord key =>
  UnionFind key value ->
  key ->
  key ->
  UnionFind key value
trivialUnion uf k1 k2 =
  fromJust $ union (error "union was too trivial") (error "union was not trivial") uf k1 k2

-- | @insert merge unionFind key value@ adds a binding from @key@ to @value@ in
-- the structure. If @key@ is already known in the structure, then @merge@ is
-- called to reconcile the known value and the new one. @merge@ receives the new
-- value as first argument.
--
insert :: Ord key =>
  (value -> value -> value) ->
  UnionFind key value ->
  key ->
  value ->
  UnionFind key value
insert merge unionFind key value =
  let (unionFind', ancestor, maybeValue) = findAncestorAndValue unionFind key in
  let newValue = maybe value (merge value) maybeValue in
  UnionFind $ Map.insert ancestor (Ancestor newValue) $ getMap unionFind'

-- | Same as @insert@ for trivial cases where one knows for sure that the key is
-- not already in the structure.
--
trivialInsert :: Ord key =>
  UnionFind key value ->
  key ->
  value ->
  UnionFind key value
trivialInsert = insert (\_ _ -> error "insert was not trivial")

-- | It is guaranteed that the right-hand side of a pair in the list of
-- equalities is the representant of an equivalence class, and therefore it
-- occurs on the left-hand side in the list of bindings.
--
toLists :: Ord key => UnionFind key value -> (UnionFind key value, [(key, key)], [(key, value)])
toLists unionFind =
  foldl
    (\(unionFind, equalities, bindings) (key, binding) ->
        case binding of
          ChildOf _ ->
            -- FIXME: this is dropping the optimised union-find.
            let (unionFind', ancestor, _) = findAncestorAndValue unionFind key in
              (unionFind', (key, ancestor) : equalities, bindings)
          Ancestor value ->
            (unionFind, equalities, (key, value) : bindings))
    (unionFind, [], [])
    (Map.toList $ getMap unionFind)
