module ListT.Extra
  ( module ListT,
    toLazyList,
    anyPath,
    allPaths,
  )
where

import ListT

toLazyList :: Monad m => ListT m a -> m [a]
toLazyList (ListT next) = do
  mayValue <- next
  case mayValue of
    Nothing -> pure []
    Just (v, rest) -> (v :) <$> toLazyList rest

anyPath :: Monad m => (a -> Bool) -> ListT m a -> m Bool
anyPath p = go
  where
    go (ListT next) = do
      mayValue <- next
      case mayValue of
        Nothing -> pure False
        Just (v, rest)
          | p v -> pure True
          | otherwise -> go rest

allPaths :: Monad m => (a -> Bool) -> ListT m a -> m Bool
allPaths p = go
  where
    go (ListT next) = do
      mayValue <- next
      case mayValue of
        Nothing -> pure True
        Just (v, rest)
          | not (p v) -> pure False
          | otherwise -> go rest
