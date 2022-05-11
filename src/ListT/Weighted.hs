{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A re-implementation of @weighted-search@
-- as a monad transformer.
module ListT.Weighted
  ( Weight (..),
    WeightedT,
    Weighted,
    weight,
    (<|>),
    toList,
  )
where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus (..), ap)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.Trans (MonadTrans (..))
import Control.Monad.WeightedSearch (Weight (..))
import Data.Foldable (fold, toList)
import Data.Functor.Identity (Identity)

-- | Weighted nondeterminstic computations over the weight @w@.
data WeightedT w m a
  = Fail
  | Yield a (WeightedT w m a)
  | Weight w (WeightedT w m a)
  | Action (m (WeightedT w m a))

type Weighted w = WeightedT w Identity

weight :: w -> WeightedT w m a -> WeightedT w m a
weight = Weight

mapWeightedT :: (Functor n) => (forall a. m a -> n a) -> WeightedT w m b -> WeightedT w n b
mapWeightedT _ Fail = Fail
mapWeightedT f (Yield x m) = Yield x (mapWeightedT f m)
mapWeightedT f (Weight w m) = Weight w (mapWeightedT f m)
mapWeightedT f (Action a) = Action (mapWeightedT f <$> f a)

instance (Functor m) => Functor (WeightedT w m) where
  fmap _ Fail = Fail
  fmap f (Yield x w) = Yield (f x) (fmap f w)
  fmap f (Weight a w) = Weight a (fmap f w)
  fmap f (Action w) = Action (fmap f <$> w)

instance (Weight w, Applicative m) => Applicative (WeightedT w m) where
  pure = return
  (<*>) = ap

instance (Weight w, Applicative m) => Monad (WeightedT w m) where
  return x = Yield x Fail
  Fail >>= _ = Fail
  Yield x m >>= f = f x `mplus` (m >>= f)
  Weight w m >>= f = Weight w (m >>= f)
  Action w >>= f = Action ((>>= f) <$> w)

instance (Weight w, Applicative m) => Alternative (WeightedT w m) where
  empty = mzero
  (<|>) = mplus

instance (Weight w, Applicative m) => MonadPlus (WeightedT w m) where
  mzero = Fail
  Fail `mplus` m = m
  Yield x m `mplus` n = Yield x (m `mplus` n)
  Weight w m `mplus` Action a = Action (mplus (Weight w m) <$> a)
  Action w `mplus` m = Action (mplus <$> w <*> pure m)
  Weight w m `mplus` Fail = Weight w m
  Weight w m `mplus` Yield x n = Yield x (Weight w m `mplus` n)
  Weight w m `mplus` Weight w' n =
    case compare w w' of
      LT -> Weight w (m `mplus` Weight (difference w' w) n)
      EQ -> Weight w (m `mplus` n)
      GT -> Weight w' (Weight (difference w w') m `mplus` n)

instance (Functor m, Foldable m) => Foldable (WeightedT w m) where
  foldMap _ Fail = mempty
  foldMap f (Yield a ms) = f a `mappend` foldMap f ms
  foldMap f (Weight _ w) = foldMap f w
  foldMap f (Action w) = fold (foldMap f <$> w)

instance (Traversable m) => Traversable (WeightedT w m) where
  sequenceA Fail = pure Fail
  sequenceA (Yield x w) = Yield <$> x <*> sequenceA w
  sequenceA (Weight a w) = Weight a <$> sequenceA w
  sequenceA (Action w) = Action <$> sequenceA (sequenceA <$> w)

instance (Weight w) => MonadTrans (WeightedT w) where
  lift x = Action (return <$> x)

instance (Weight w, MonadIO m) => MonadIO (WeightedT w m) where
  liftIO x = Action (return <$> liftIO x)

instance (Weight w, MonadState s m) => MonadState s (WeightedT w m) where
  get = lift get
  put = lift . put

instance (Weight w, MonadReader r m) => MonadReader r (WeightedT w m) where
  ask = lift ask
  local f = mapWeightedT (local f)

{-
instance forall s w m. (Weight w, MonadWriter s m) => MonadWriter s (WeightedT w m) where
  tell = lift . tell
  listen = go mempty
    where
      go :: s -> WeightedT w m a -> WeightedT w m (a, s)
      go _acc Fail = Fail
      go acc (Yield x m) = Yield (x, acc) (go acc m)
      go acc (Weight w m) = Weight w (go acc m)
      go acc (Action a) = Action $ do
        (w, r) <- listen a
        pure $ go (acc <> r) w
  pass = ???
-}
