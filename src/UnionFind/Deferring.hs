module UnionFind.Deferring
  ( applyActionsWithDeferring,
    unionWithDeferring,
    insertWithDeferring,
  )
where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (get, put)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT)
import UnionFind (WithUnionFindT)
import qualified UnionFind as UF
import UnionFind.Action (Action (..))

applyActionsWithDeferring ::
  (Ord key, Monad m) =>
  (value -> value -> WriterT [Action key value] m value) ->
  [Action key value] ->
  WithUnionFindT key value m ()
applyActionsWithDeferring _ [] = return ()
applyActionsWithDeferring merge (action : actions) = do
  moreActions <- applyActionWithDeferring merge action
  applyActionsWithDeferring merge moreActions
  applyActionsWithDeferring merge actions

applyActionWithDeferring ::
  (Ord key, Monad m) =>
  (value -> value -> WriterT [Action key value] m value) ->
  Action key value ->
  WithUnionFindT key value m [Action key value]
applyActionWithDeferring merge action = do
  unionFind <- get
  let writer = UF.runWithUnionFindT unionFind $ UF.applyActionWithM merge action
  (((), unionFind'), actions) <- lift $ runWriterT writer
  put unionFind'
  return actions

unionWithDeferring ::
  (Ord key, Monad m) =>
  (value -> value -> WriterT [Action key value] m value) ->
  key ->
  key ->
  WithUnionFindT key value m ()
unionWithDeferring merge key1 key2 = applyActionsWithDeferring merge [Union key1 key2]

insertWithDeferring ::
  (Ord key, Monad m) =>
  (value -> value -> WriterT [Action key value] m value) ->
  key ->
  value ->
  WithUnionFindT key value m ()
insertWithDeferring merge key value = applyActionsWithDeferring merge [Insert key value]
