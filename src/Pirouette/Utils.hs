{-# LANGUAGE TupleSections #-}

module Pirouette.Utils where

import Data.Maybe

secondM :: (Functor m) => (b -> m b') -> (a, b) -> m (a, b')
secondM f (a, b) = (a,) <$> f b

mapMaybeM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f = fmap catMaybes . mapM f
