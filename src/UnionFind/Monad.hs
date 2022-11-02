{-# LANGUAGE LambdaCase #-}

module UnionFind.Monad where

import Control.Monad.Trans.State.Strict (StateT, get, put, runState, runStateT)
import Data.Functor.Identity (Identity)
import Data.Map (Map)
import qualified Data.Map as Map
import UnionFind.Action (Action (..))
import UnionFind.Internal (UnionFind (..), UnionFindCell (..), empty)

type WithUnionFindT key value = StateT (UnionFind key value)

type WithUnionFind key value = WithUnionFindT key value Identity

runWithUnionFindT ::
  Monad m =>
  WithUnionFindT key value m result ->
  m (result, UnionFind key value)
runWithUnionFindT f = runStateT f empty

runWithUnionFind ::
  WithUnionFind key value result ->
  (result, UnionFind key value)
runWithUnionFind f = runState f empty

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
--
-- FIXME: Implement the optimisation for future calls
find ::
  (Ord key, Monad m) =>
  key ->
  WithUnionFindT key value m (key, Maybe value)
find key =
  Map.lookup key <$> getBindings >>= \case
    Nothing -> return (key, Nothing)
    Just (ChildOf key') ->
      -- We use @findExn@ because invariant (ii) guarantees that it will
      -- succeed. If it ever raises an exception, then we found a bug.
      findExn key'
    Just (Ancestor maybeValue) -> return (key, maybeValue)

-- | Same as @find@ but fails where there is no value associated to the given
-- key. Prefer using @find@ or @lookup@.
--
-- FIXME: Implement the optimisation for future calls
findExn ::
  (Ord key, Monad m) =>
  key ->
  WithUnionFindT key value m (key, Maybe value)
findExn key =
  Map.lookup key <$> getBindings >>= \case
    Nothing -> error "findExn: no value associated with key"
    Just (ChildOf key') -> findExn key'
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
unionWithM merge key1 key2 unionFind = do
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
        value <- merge value1 value2
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
  newValue <- maybe (return value) (merge value) maybeValue
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
