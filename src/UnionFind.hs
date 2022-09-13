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
  | Ancestor
  | AncestorWith value

-- | A persistent union-find data structure.
--
-- Invariants:
--
--   (i) There are no cycles.
--   (ii) Keys under @ChildOf@ are present in the map.
--
-- The points (i) and (ii) imply that, if a key is present in the map, then
-- there is a path made of @ChildOf@ constructors from that key to an @Ancestor@
-- or @AncestorWith@ constructor.
newtype UnionFind key value = UnionFind
  { getMap :: Map key (UnionFindCell key value)
  }

instance Default (UnionFind key value) where
  def = empty

instance (Pretty key, Pretty value) => Pretty (UnionFind key value) where
  pretty unionFind =
    vsep $ map (uncurry prettyBinding) (Map.toList $ getMap unionFind)
    where
      prettyBinding key1 (ChildOf key2) = pretty key1 <+> "~~" <+> pretty key2
      prettyBinding key (AncestorWith value) = pretty key <+> ":=" <+> pretty value

-- | The empty union-find that does not know of any equivalences or values.
empty :: UnionFind key value
empty = UnionFind Map.empty

-- | @find key unionFind@ finds the ancestor and value associated to @key@ in
-- the @unionFind@ structure. It returns a new union-find structure with the
-- same semantics but optimised for future calls, the ancestor for @key@ and the
-- found value, @Just Nothing@ if the @key@ is in the structure but without
-- binding, or @Nothing@ if @key@ is not in the structure.
--
-- Prefer using @lookup@.
--
-- FIXME: Maybe we prefer a custom type instead of `Maybe (Maybe value)`?
-- FIXME: Implement the optimisation for future calls
find ::
  Ord key =>
  key ->
  UnionFind key value ->
  (UnionFind key value, key, Maybe (Maybe value))
find key unionFind =
  case Map.lookup key $ getMap unionFind of
    Nothing -> (unionFind, key, Nothing)
    Just (ChildOf key') -> find key' unionFind -- will be @Just@
    Just Ancestor -> (unionFind, key, Just Nothing)
    Just (AncestorWith value) -> (unionFind, key, Just $ Just value)

-- | @lookup key unionFind@ is the same as @find@ but it does not return the
-- ancestor.
lookup ::
  Ord key =>
  key ->
  UnionFind key value ->
  (UnionFind key value, Maybe (Maybe value))
lookup key unionFind =
  let (unionFind', _, maybeValue) = find key unionFind
   in (unionFind', maybeValue)

-- | @union merge unionFind key1 key2@ merges together the equivalence classes
-- of @key1@ and @key2@ in @unionFind@, thus adding the information that @key1@
-- and @key2@ are equivalent, and returns an updated union-find structure.
--
-- - If neither @key1@ nor @key2@ exists in @unionFind@, they are inserted as
--   equivalent and without value.
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
union ::
  Ord key =>
  (value -> value -> value) ->
  key ->
  key ->
  UnionFind key value ->
  UnionFind key value
union merge key1 key2 unionFind =
  let (unionFind1, ancestor1, maybeValue1) = find key1 unionFind
   in let (unionFind2, ancestor2, maybeValue2) = find key2 unionFind1
       in if ancestor1 == ancestor2
            then unionFind2
            else
              let onUnionFind2sMap update = UnionFind $ update $ getMap $ unionFind2
               in case (join maybeValue1, join maybeValue2) of
                    (Nothing, Nothing) ->
                      onUnionFind2sMap $
                        Map.insert key1 (ChildOf key2)
                          . Map.insert key2 Ancestor
                    (Just _, Nothing) ->
                      onUnionFind2sMap $ Map.insert key2 (ChildOf key1)
                    (Nothing, Just _) ->
                      onUnionFind2sMap $ Map.insert key1 (ChildOf key2)
                    (Just value1, Just value2) ->
                      -- FIXME: Implement the optimisation that choses which key should be the
                      -- other's child by keeping track of the size of the equivalence classes.
                      onUnionFind2sMap $
                        Map.insert key1 (ChildOf key2)
                          . Map.insert key2 (AncestorWith $ merge value1 value2)

-- | Same as @union@ for trivial cases where one knows for sure that the keys
-- are not in the same equivalence class (or one is absent).
trivialUnion ::
  Ord key =>
  key ->
  key ->
  UnionFind key value ->
  UnionFind key value
trivialUnion = union (\_ _ -> error "union was not trivial")

-- | @insert merge unionFind key value@ adds a binding from @key@ to @value@ in
-- the structure. If @key@ is already known in the structure, then @merge@ is
-- called to reconcile the known value and the new one. @merge@ receives the new
-- value as first argument.
insert ::
  Ord key =>
  (value -> value -> value) ->
  key ->
  value ->
  UnionFind key value ->
  UnionFind key value
insert merge key value unionFind =
  let (unionFind', ancestor, maybeValue) = find key unionFind
   in let newValue = maybe value (merge value) (join maybeValue)
       in UnionFind $ Map.insert ancestor (AncestorWith newValue) $ getMap unionFind'

-- | Same as @insert@ for trivial cases where one knows for sure that the key is
-- not already in the structure.
trivialInsert ::
  Ord key =>
  key ->
  value ->
  UnionFind key value ->
  UnionFind key value
trivialInsert = insert (\_ _ -> error "insert was not trivial")

-- | It is guaranteed that the right-hand side of a pair in the list of
-- equalities is the representant of an equivalence class, and therefore it
-- occurs on the left-hand side in the list of bindings.
toLists :: Ord key => UnionFind key value -> (UnionFind key value, [(key, key)], [(key, value)])
toLists unionFind =
  foldl
    ( \(unionFind, equalities, bindings) (key, binding) ->
        case binding of
          ChildOf _ ->
            -- FIXME: this is dropping the optimised union-find.
            let (unionFind', ancestor, _) = find key unionFind
             in (unionFind', (key, ancestor) : equalities, bindings)
          Ancestor ->
            (unionFind, equalities, bindings)
          AncestorWith value ->
            (unionFind, equalities, (key, value) : bindings)
    )
    (unionFind, [], [])
    (Map.toList $ getMap unionFind)

join :: Maybe (Maybe value) -> Maybe value
join Nothing = Nothing
join (Just Nothing) = Nothing
join (Just (Just value)) = Just value
