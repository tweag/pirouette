{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module UnionFind
  ( UnionFind,
    empty,
    lookup,
    unionWith,
    trivialUnion,
    union,
    insertWith,
    trivialInsert,
    insert,
    toLists,
    toList,
  )
where

import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid ((<>))
import Data.Semigroup (Semigroup)
import Data.Tuple (snd, swap)
import Prettyprinter (Pretty (pretty), vsep, (<+>))
import UnionFind.Internal
  ( UnionFind (..),
    UnionFindCell (..),
    empty,
  )
import UnionFind.Monadic (runWithUnionFind)
import qualified UnionFind.Monadic as Monadic
import Prelude (Maybe (..), Ord, error, foldl, map, uncurry, ($))

instance (Ord key, Pretty key, Pretty value) => Pretty (UnionFind key value) where
  pretty unionFind =
    let (_, unionFindL) = toList unionFind
     in vsep $ map (uncurry prettyEqClassAndValue) unionFindL
    where
      prettyEqClassAndValue eqClass Nothing =
        prettyEqClass eqClass
      prettyEqClassAndValue eqClass (Just value) =
        prettyEqClass eqClass <+> ":=" <+> pretty value
      prettyEqClass eqClass =
        foldl
          (\p key -> p <+> "~~" <+> pretty key)
          (pretty (NonEmpty.head eqClass))
          (NonEmpty.tail eqClass)

find ::
  Ord key =>
  key ->
  UnionFind key value ->
  (UnionFind key value, key, Maybe value)
find key unionFind =
  let ((ancestor, maybeValue), unionFind') = runWithUnionFind unionFind $ Monadic.find key
   in (unionFind', ancestor, maybeValue)

lookup ::
  Ord key =>
  key ->
  UnionFind key value ->
  (UnionFind key value, Maybe value)
lookup key unionFind = swap $ runWithUnionFind unionFind $ Monadic.lookup key

unionWith ::
  Ord key =>
  (value -> value -> value) ->
  key ->
  key ->
  UnionFind key value ->
  UnionFind key value
unionWith merge key1 key2 unionFind =
  snd $ runWithUnionFind unionFind $ Monadic.unionWith merge key1 key2

trivialUnion ::
  Ord key =>
  key ->
  key ->
  UnionFind key value ->
  UnionFind key value
trivialUnion = unionWith (\_ _ -> error "union was not trivial")

union ::
  (Ord key, Data.Semigroup.Semigroup value) =>
  key ->
  key ->
  UnionFind key value ->
  UnionFind key value
union = unionWith (<>)

insertWith ::
  Ord key =>
  (value -> value -> value) ->
  key ->
  value ->
  UnionFind key value ->
  UnionFind key value
insertWith merge key value unionFind =
  snd $ runWithUnionFind unionFind $ Monadic.insertWith merge key value

trivialInsert ::
  Ord key =>
  key ->
  value ->
  UnionFind key value ->
  UnionFind key value
trivialInsert = insertWith (\_ _ -> error "insert was not trivial")

insert ::
  (Ord key, Semigroup value) =>
  key ->
  value ->
  UnionFind key value ->
  UnionFind key value
insert = insertWith (<>)

-- | @toLists unionFind@ returns a pair of of lists as well as a new union-find
-- structure optimised for future calls.
--
-- - The first list contains pairs of keys, where the right-hand side is the
--   representative of an equivalence class and the left-hand side is an element
--   of the class. In case of singleton equivalence class, no binding appears in
--   this list.
--
-- - The second list contains bindings from representative of an equivalence
--   class to the associated value. In case of an equivalence class without
--   binding, nothing appears in this list.
--
-- Unless you really want this low-level interface, prefer @toList@.
toLists ::
  Ord key =>
  UnionFind key value ->
  (UnionFind key value, [(key, key)], [(key, value)])
toLists unionFind =
  foldl gobble (unionFind, [], []) (Map.toList $ getMap unionFind)
  where
    gobble ::
      Ord key =>
      (UnionFind key value, [(key, key)], [(key, value)]) ->
      (key, UnionFindCell key value) ->
      (UnionFind key value, [(key, key)], [(key, value)])
    gobble
      (unionFind', equalities, bindings)
      (key, binding) =
        case binding of
          ChildOf _ ->
            let (unionFind'', ancestor, _) = find key unionFind'
             in (unionFind'', (key, ancestor) : equalities, bindings)
          Ancestor Nothing ->
            (unionFind', equalities, bindings)
          Ancestor (Just value) ->
            (unionFind', equalities, (key, value) : bindings)

-- | @toList unionFind@ returns a list representing the mappings in @unionFind@
-- as well as a new union-find structure optimised for future calls. The
-- mappings are pairs, the left-hand side being a non-empty list of all the
-- @key@s in an equivalence class and the right-hand side being the value
-- associated with this equivalence class, or @Nothing@ if there is no such
-- value.
--
-- In particular, @([key], Just value)@ represents the equivalence class
-- containing only @key@ and bound to @value@ while @(keys, Nothing)@ represents
-- the equivalence class containing all @keys@ but not bound to any value.
--
-- There are no occurrences of @[]@ of the left-hand side and there are no
-- occurrences of a pair @([key], Nothing)@. Additionally, all the left-hand
-- side lists are disjoint. The order of keys in those lists is not specified.
toList ::
  Ord key =>
  UnionFind key value ->
  (UnionFind key value, [(NonEmpty key, Maybe value)])
toList unionFind =
  let (unionFind', bindings) =
        foldl gobble (unionFind, Map.empty) (Map.toList $ getMap unionFind)
   in ( unionFind',
        Map.toList bindings
          & map
            ( \(ancestor, (otherKeys, maybeValue)) ->
                (NonEmpty.insert ancestor otherKeys, maybeValue)
            )
      )
  where
    gobble ::
      Ord key =>
      (UnionFind key value, Map key ([key], Maybe value)) ->
      (key, UnionFindCell key value) ->
      (UnionFind key value, Map key ([key], Maybe value))
    gobble (unionFind', bindings) (key, binding) =
      case binding of
        ChildOf _ ->
          let (unionFind'', ancestor, _) = find key unionFind'
           in (unionFind'', addKeyToBindings key ancestor bindings)
        Ancestor Nothing ->
          (unionFind', bindings)
        Ancestor (Just value) ->
          (unionFind', addValueToBindings value key bindings)
    -- @addKeyToBindings key ancestor bindings@ adds @key@ to the equivalence
    -- class of @ancestor@ in @bindings@, creating this equivalence class if
    -- necessary.
    addKeyToBindings ::
      Ord key =>
      key ->
      key ->
      Map key ([key], Maybe value) ->
      Map key ([key], Maybe value)
    addKeyToBindings key =
      Map.alter
        ( \case
            Nothing -> Just ([key], Nothing)
            Just (keys, mValue) -> Just (key : keys, mValue)
        )
    -- @addValueToBindings value ancestor bindings@ binds @value@ to @ancestor@
    -- in @bindings@, creating the binding if necessary.
    addValueToBindings ::
      Ord key =>
      value ->
      key ->
      Map key ([key], Maybe value) ->
      Map key ([key], Maybe value)
    addValueToBindings value =
      Map.alter
        ( \case
            Nothing -> Just ([], Just value)
            Just (keys, Nothing) -> Just (keys, Just value)
            _ -> error "two bindings for the same ancestor"
        )
