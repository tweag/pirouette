module UnionFind.Monad where

import qualified Control.Monad.Trans.State.Strict as S
import Data.Functor.Identity (Identity)
import qualified UnionFind.Internal as UF

type WithUnionFindT key value = S.StateT (UF.UnionFind key value)

type WithUnionFind key value = WithUnionFindT key value Identity

runWithUnionFindT ::
  Monad m =>
  WithUnionFindT key value m result ->
  m (result, UF.UnionFind key value)
runWithUnionFindT f = S.runStateT f UF.empty

runWithUnionFind ::
  WithUnionFind key value result ->
  (result, UF.UnionFind key value)
runWithUnionFind f = S.runState f UF.empty

lookup ::
  (Ord key, Monad m) =>
  key ->
  WithUnionFindT key value m (Maybe value)
lookup key = do
  unionFind <- S.get
  let (unionFind', result) = UF.lookup key unionFind
  S.put unionFind'
  return result

unionWith ::
  (Ord key, Monad m) =>
  (value -> value -> value) ->
  key ->
  key ->
  WithUnionFindT key value m ()
unionWith merge key1 key2 =
  S.modify' $ UF.unionWith merge key1 key2

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
  S.modify' $ UF.insertWith merge key value

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
