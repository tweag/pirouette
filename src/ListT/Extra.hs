module ListT.Extra
  ( module ListT,
    toLazyList,
  )
where

import ListT

toLazyList :: Monad m => ListT m a -> m [a]
toLazyList (ListT next) = do
  mayValue <- next
  case mayValue of
    Nothing -> pure []
    Just (v, rest) -> (v :) <$> toLazyList rest
