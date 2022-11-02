module UnionFind.Monad where

import Control.Monad.Trans.Class (MonadTrans (lift))
import Control.Monad.Trans.State.Strict (StateT, get, modify', put, runState, runStateT)
import Data.Functor.Identity (Identity)
import UnionFind.Action
import qualified UnionFind.Internal as UF

type WithUnionFindT key value = StateT (UF.UnionFind key value)

type WithUnionFind key value = WithUnionFindT key value Identity

runWithUnionFindT ::
  Monad m =>
  WithUnionFindT key value m result ->
  m (result, UF.UnionFind key value)
runWithUnionFindT f = runStateT f UF.empty

runWithUnionFind ::
  WithUnionFind key value result ->
  (result, UF.UnionFind key value)
runWithUnionFind f = runState f UF.empty

lookup ::
  (Ord key, Monad m) =>
  key ->
  WithUnionFindT key value m (Maybe value)
lookup key = do
  unionFind <- get
  let (unionFind', result) = UF.lookup key unionFind
  put unionFind'
  return result

unionWith ::
  (Ord key, Monad m) =>
  (value -> value -> value) ->
  key ->
  key ->
  WithUnionFindT key value m ()
unionWith merge key1 key2 =
  modify' $ UF.unionWith merge key1 key2

unionWithM ::
  (Ord key, Monad m) =>
  (value -> value -> m value) ->
  key ->
  key ->
  WithUnionFindT key value m ()
unionWithM merge key1 key2 = do
  uf <- get
  uf' <- lift $ UF.unionWithM merge key1 key2 uf
  put uf'

trivialUnion ::
  (Ord key, Monad m) =>
  key ->
  key ->
  WithUnionFindT key value m ()
trivialUnion = unionWith (\_ _ -> error "union was not trivial")

union ::
  (Ord key, Semigroup value, Monad m) =>
  key ->
  key ->
  WithUnionFindT key value m ()
union = unionWith (<>)

insertWith ::
  (Ord key, Monad m) =>
  (value -> value -> value) ->
  key ->
  value ->
  WithUnionFindT key value m ()
insertWith merge key value =
  modify' $ UF.insertWith merge key value

trivialInsert ::
  (Ord key, Monad m) =>
  key ->
  value ->
  WithUnionFindT key value m ()
trivialInsert = insertWith (\_ _ -> error "insert was not trivial")

insert ::
  (Ord key, Semigroup value, Monad m) =>
  key ->
  value ->
  WithUnionFindT key value m ()
insert = insertWith (<>)

applyActionWith ::
  (Ord key, Monad m) =>
  (value -> value -> value) ->
  Action key value ->
  WithUnionFindT key value m ()
applyActionWith merge (Union k1 k2) = unionWith merge k1 k2
applyActionWith merge (Insert k v) = insertWith merge k v

-- | Same as @applyActionWith@ but uses @(<>)@ to merge values.
applyAction ::
  (Ord key, Semigroup value, Monad m) =>
  Action key value ->
  WithUnionFindT key value m ()
applyAction = applyActionWith (<>)
