{-# LANGUAGE DeriveFunctor #-}
module Pirouette.Monad.Maybe where

import Data.Maybe
import Control.Monad.Trans
import Control.Applicative

newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }
  deriving (Functor)

wrapMaybe :: (Applicative m) => Maybe a -> MaybeT m a
wrapMaybe = MaybeT . pure

-- |Returns '()' when its argument fails.
notM :: (Monad m) => MaybeT m a -> MaybeT m ()
notM (MaybeT mma) = MaybeT $ mma >>= maybe (return $ Just ())
                                           (const $ return Nothing)

mapMaybeM :: (Monad m) => (a -> MaybeT m b) -> [a] -> m [b]
mapMaybeM f = fmap catMaybes . mapM (runMaybeT . f)

instance Applicative m => Applicative (MaybeT m) where
  pure = MaybeT . pure . Just

  (MaybeT f) <*> (MaybeT xs) = MaybeT $ fmap delay f <*> xs
    where delay :: Maybe (a -> b) -> Maybe a -> Maybe b
          delay _ Nothing  = Nothing
          delay mf (Just a) = fmap ($ a) mf

instance Monad m => Monad (MaybeT m) where
  x >>= f = MaybeT $ runMaybeT x >>= maybe (return Nothing) (runMaybeT . f)

instance MonadTrans MaybeT where
  lift = MaybeT . fmap Just

instance (Monad m) => MonadFail (MaybeT m) where
  fail _ = wrapMaybe Nothing

instance (Monad m) => Alternative (MaybeT m) where
  empty = wrapMaybe Nothing
  MaybeT x <|> MaybeT y = MaybeT $ x >>= maybe y (return . Just)
