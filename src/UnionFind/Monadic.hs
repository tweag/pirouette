{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module UnionFind.Monadic where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalState, evalStateT, execState, execStateT, get, put, runState, runStateT)
import Data.Foldable (foldlM)
import Data.Function ((&))
import Data.Functor.Identity (Identity)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Prettyprinter (Pretty (pretty), vsep, (<+>))
import UnionFind.Action (Action (..))
import UnionFind.Internal (UnionFind (..), UnionFindCell (..), empty)

instance (Ord key, Pretty key, Pretty value) => Pretty (UnionFind key value) where
  pretty unionFind =
    let unionFindL = fst $ runWithUnionFind unionFind toList
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

type WithUnionFindT key value = StateT (UnionFind key value)

type WithUnionFind key value = WithUnionFindT key value Identity

runWithUnionFindT :: Monad m => UnionFind key value -> WithUnionFindT key value m result -> m (result, UnionFind key value)
runWithUnionFindT = flip runStateT

evalWithUnionFindT :: Monad m => UnionFind key value -> WithUnionFindT key value m result -> m result
evalWithUnionFindT = flip evalStateT

execWithUnionFindT :: Monad m => UnionFind key value -> WithUnionFindT key value m result -> m (UnionFind key value)
execWithUnionFindT = flip execStateT

runWithEmptyUnionFindT :: Monad m => WithUnionFindT key value m result -> m (result, UnionFind key value)
runWithEmptyUnionFindT = runWithUnionFindT empty

evalWithEmptyUnionFindT :: Monad m => WithUnionFindT key value m result -> m result
evalWithEmptyUnionFindT = evalWithUnionFindT empty

execWithEmptyUnionFindT :: Monad m => WithUnionFindT key value m result -> m (UnionFind key value)
execWithEmptyUnionFindT = execWithUnionFindT empty

runWithUnionFind :: UnionFind key value -> WithUnionFind key value result -> (result, UnionFind key value)
runWithUnionFind = flip runState

evalWithUnionFind :: UnionFind key value -> WithUnionFind key value result -> result
evalWithUnionFind = flip evalState

execWithUnionFind :: UnionFind key value -> WithUnionFind key value result -> UnionFind key value
execWithUnionFind = flip execState

runWithEmptyUnionFind :: WithUnionFind key value result -> (result, UnionFind key value)
runWithEmptyUnionFind = runWithUnionFind empty

evalWithEmptyUnionFind :: WithUnionFind key value result -> result
evalWithEmptyUnionFind = evalWithUnionFind empty

execWithEmptyUnionFind :: WithUnionFind key value result -> UnionFind key value
execWithEmptyUnionFind = execWithUnionFind empty

-- | Helper that gets the bindings from the state.
getBindings ::
  Monad m =>
  WithUnionFindT key value m (Map key (UnionFindCell key value))
getBindings = getMap <$> get

-- | Helper that puts the bindings from the state.
putBindings ::
  Monad m =>
  Map key (UnionFindCell key value) ->
  WithUnionFindT key value m ()
putBindings = put . UnionFind

-- | Helper that updates the bindings from the state.
updateBindings ::
  Monad m =>
  (Map key (UnionFindCell key value) -> Map key (UnionFindCell key value)) ->
  WithUnionFindT key value m ()
updateBindings f = do
  bindings <- getBindings
  let newBindings = f bindings
  putBindings newBindings

-- | @find key@ finds the ancestor and value associated to @key@ in the
-- union-find structure. It returns the ancestor for @key@ and the found value
-- or @Nothing@ if there is no such value.
--
-- Prefer using @lookup@.
find ::
  (Ord key, Monad m) =>
  key ->
  WithUnionFindT key value m (key, Maybe value)
find key =
  Map.lookup key <$> getBindings >>= \case
    Nothing -> return (key, Nothing)
    Just (ChildOf key') -> do
      -- We use @findExn@ because invariant (ii) guarantees that it will
      -- succeed. If it ever raises an exception, then we found a bug.
      (ancestor, maybeValue) <- findExn key'
      updateBindings $ Map.insert key $ ChildOf ancestor
      return (ancestor, maybeValue)
    Just (Ancestor maybeValue) -> return (key, maybeValue)

-- | Same as @find@ but fails where there is no value associated to the given
-- key. Prefer using @find@ or @lookup@.
findExn ::
  (Ord key, Monad m) =>
  key ->
  WithUnionFindT key value m (key, Maybe value)
findExn key =
  Map.lookup key <$> getBindings >>= \case
    Nothing -> error "findExn: no value associated with key"
    Just (ChildOf key') -> do
      (ancestor, maybeValue) <- findExn key'
      updateBindings $ Map.insert key $ ChildOf ancestor
      return (ancestor, maybeValue)
    Just (Ancestor maybeValue) -> return (key, maybeValue)

-- | @lookup key@ returns the value associated to @key@ in the union-find
-- structure, or @Nothing@ if there is no such binding.
lookup ::
  (Ord key, Monad m) =>
  key ->
  WithUnionFindT key value m (Maybe value)
lookup key = snd <$> find key

-- | @unionWith merge key1 key2@ merges together the equivalence classes of
-- @key1@ and @key2@ in the union-find structure, thus adding the information
-- that @key1@ and @key2@ are equivalent.
--
-- - If neither @key1@ nor @key2@ exists in the union-find structure, they are
--   inserted as equivalent and without value.
--
-- - If either @key1@ or @key2@ exists in the union-find structure but not the
--   other key, the other key is added transparently to the existing key's
--   equivalence class.
--
-- - If both @key1@ and @key2@ exist in the union-find structure in the same
--   equivalence class, nothing changes.
--
-- - If both @key1@ and @key2@ exist in the union-find structure in distinct
--   equivalence classes, the function @merge@ is called to reconcile the two
--   values associated to the two equivalence classes. @merge@ receives the
--   value associated to @key1@'s equivalence class as first argument and the
--   value associated to @key2@'s equivalence class as second argument.
unionWith ::
  (Ord key, Monad m) =>
  (value -> value -> value) ->
  key ->
  key ->
  WithUnionFindT key value m ()
unionWith merge = unionWithM (\value1 value2 -> return $ merge value1 value2)

-- | @unionWithM@ is the same as @unionWith@ but for a monadic merge function.
unionWithM ::
  (Ord key, Monad m) =>
  (value -> value -> m value) ->
  key ->
  key ->
  WithUnionFindT key value m ()
unionWithM merge key1 key2 = do
  (ancestor1, maybeValue1) <- find key1
  (ancestor2, maybeValue2) <- find key2
  if ancestor1 == ancestor2
    then return ()
    else case (maybeValue1, maybeValue2) of
      (Nothing, Nothing) ->
        updateBindings $
          Map.insert ancestor1 (ChildOf ancestor2)
            . Map.insert ancestor2 (Ancestor Nothing)
      (Just _, Nothing) ->
        updateBindings $ Map.insert ancestor2 (ChildOf ancestor1)
      (Nothing, Just _) ->
        updateBindings $ Map.insert ancestor1 (ChildOf ancestor2)
      (Just value1, Just value2) -> do
        -- FIXME: Implement the optimisation that choses which key should be
        -- the other's child by keeping track of the size of the equivalence
        -- classes.
        value <- lift $ merge value1 value2
        updateBindings $
          Map.insert ancestor1 (ChildOf ancestor2)
            . Map.insert ancestor2 (Ancestor $ Just value)

-- | Same as @unionWith@ for trivial cases where one knows for sure that the
-- keys are not in the same equivalence class (or one is absent).
trivialUnion ::
  (Ord key, Monad m) =>
  key ->
  key ->
  WithUnionFindT key value m ()
trivialUnion = unionWith (\_ _ -> error "union was not trivial")

-- | Same as @unionWith@ but uses @(<>)@ to merge values.
union ::
  (Ord key, Monad m, Semigroup value) =>
  key ->
  key ->
  WithUnionFindT key value m ()
union = unionWith (<>)

-- | @insertWith merge key value@ adds a binding from @key@ to @value@ in the
-- union-find structure. If @key@ is already known in the union-find structure,
-- then @merge@ is called to reconcile the known value and the new one. @merge@
-- receives the new value as first argument.
insertWith ::
  (Ord key, Monad m) =>
  (value -> value -> value) ->
  key ->
  value ->
  WithUnionFindT key value m ()
insertWith merge = insertWithM (\value1 value2 -> return $ merge value1 value2)

-- | @insertWithM@ is the same as @insertWith@ but for a monadic merge function.
insertWithM ::
  (Ord key, Monad m) =>
  (value -> value -> m value) ->
  key ->
  value ->
  WithUnionFindT key value m ()
insertWithM merge key value = do
  (ancestor, maybeValue) <- find key
  newValue <- lift $ maybe (return value) (merge value) maybeValue
  updateBindings $ Map.insert ancestor (Ancestor $ Just newValue)

-- | Same as @insertWith@ for trivial cases where one knows for sure that the
-- key is not already in the structure.
trivialInsert ::
  (Ord key, Monad m) =>
  key ->
  value ->
  WithUnionFindT key value m ()
trivialInsert = insertWith (\_ _ -> error "insert was not trivial")

-- | Same as @insertWith@ but uses @(<>)@ to merge values.
insert ::
  (Ord key, Monad m, Semigroup value) =>
  key ->
  value ->
  WithUnionFindT key value m ()
insert = insertWith (<>)

-- | @applyActionWith merge action@ applies @action@ to the union-find structure
-- using the @merge@ function.
applyActionWith ::
  (Ord key, Monad m) =>
  (value -> value -> value) ->
  Action key value ->
  WithUnionFindT key value m ()
applyActionWith merge = applyActionWithM (\value1 value2 -> return $ merge value1 value2)

-- | Same as @applyActionWith@ but for a monadic merge function.
applyActionWithM ::
  (Ord key, Monad m) =>
  (value -> value -> m value) ->
  Action key value ->
  WithUnionFindT key value m ()
applyActionWithM merge (Union key1 key2) = unionWithM merge key1 key2
applyActionWithM merge (Insert key value) = insertWithM merge key value

-- | Same as @applyActionWith@ but uses @(<>)@ to merge values.
applyAction ::
  (Ord key, Monad m, Semigroup value) =>
  Action key value ->
  WithUnionFindT key value m ()
applyAction = applyActionWith (<>)

-- | @toList@ returns a list representing the mappings in the union-find
-- structure. The mappings are pairs, the left-hand side being a non-empty list
-- of all the @key@s in an equivalence class and the right-hand side being the
-- value associated with this equivalence class, or @Nothing@ if there is no
-- such value.
--
-- In particular, @([key], Just value)@ represents the equivalence class
-- containing only @key@ and bound to @value@ while @(keys, Nothing)@ represents
-- the equivalence class containing all @keys@ but not bound to any value.
--
-- There are no occurrences of @[]@ of the left-hand side and there are no
-- occurrences of a pair @([key], Nothing)@. Additionally, all the left-hand
-- side lists are disjoint. The order of keys in those lists is not specified.
toList ::
  (Ord key, Monad m) =>
  WithUnionFindT key value m [(NonEmpty key, Maybe value)]
toList = do
  bindings <- getBindings
  bindings' <- foldlM gobble Map.empty $ Map.toList bindings
  return $
    Map.toList bindings'
      & map
        ( \(ancestor, (otherKeys, maybeValue)) ->
            (NonEmpty.insert ancestor otherKeys, maybeValue)
        )
  where
    gobble ::
      (Ord key, Monad m) =>
      Map key ([key], Maybe value) ->
      (key, UnionFindCell key value) ->
      WithUnionFindT key value m (Map key ([key], Maybe value))
    gobble bindings (key, binding) =
      case binding of
        ChildOf _ -> do
          (ancestor, _) <- find key
          return $ addKeyToBindings key ancestor bindings
        Ancestor Nothing ->
          return bindings
        Ancestor (Just value) ->
          return $ addValueToBindings value key bindings
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

-- | @toLists@ returns a pair of lists:
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
  (Ord key, Monad m) =>
  WithUnionFindT key value m ([(key, key)], [(key, value)])
toLists = do
  bindings <- getBindings
  foldlM gobble ([], []) $ Map.toList bindings
  where
    gobble ::
      (Ord key, Monad m) =>
      ([(key, key)], [(key, value)]) ->
      (key, UnionFindCell key value) ->
      WithUnionFindT key value m ([(key, key)], [(key, value)])
    gobble (equalities, bindings) (key, binding) =
      case binding of
        ChildOf _ -> do
          (ancestor, _) <- find key
          return ((key, ancestor) : equalities, bindings)
        Ancestor Nothing ->
          return (equalities, bindings)
        Ancestor (Just value) ->
          return (equalities, (key, value) : bindings)
