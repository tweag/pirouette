{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A re-implementation of @weighted-search@
-- as a monad transformer.
module ListT.Weighted
  ( WeightedListT(..),
    WeightedList,
    MonadWeightedList (..),
    (<|>),
    mapWeightedListT,
    toList,
    firstThat,
  )
where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus (..), ap)
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Reader (MonadReader (..), ReaderT (..))
import Control.Monad.State (MonadState (..), StateT (..))
import Control.Monad.Trans (MonadTrans (..))
import Control.Monad.Writer (WriterT (..))
import Data.Foldable (fold)
import Data.Functor.Identity (Identity)
import GHC.Natural

-- | Weighted nondeterminstic computations over the weight @w@.
data WeightedListT m a
  = Fail
  | -- | returns one value, and then more of them
    Yield a (WeightedListT m a)
  | -- | signals that the internal computation is weighted
    Weight Natural (WeightedListT m a)
  | -- | perform an action
    Action (m (WeightedListT m a))

type WeightedList = WeightedListT Identity

mapWeightedListT :: (Functor n) => (forall a. m a -> n a) -> WeightedListT m b -> WeightedListT n b
mapWeightedListT _ Fail = Fail
mapWeightedListT f (Yield x m) = Yield x (mapWeightedListT f m)
mapWeightedListT f (Weight w m) = Weight w (mapWeightedListT f m)
mapWeightedListT f (Action a) = Action (mapWeightedListT f <$> f a)

instance (Functor m) => Functor (WeightedListT m) where
  fmap _ Fail = Fail
  fmap f (Yield x w) = Yield (f x) (fmap f w)
  fmap f (Weight a w) = Weight a (fmap f w)
  fmap f (Action w) = Action (fmap f <$> w)

instance (Functor m) => Applicative (WeightedListT m) where
  pure = return
  (<*>) = ap

instance (Functor m) => Monad (WeightedListT m) where
  return x = Yield x Fail
  Fail >>= _ = Fail
  Yield x m >>= f = f x `mplus` (m >>= f)
  Weight w m >>= f = Weight w (m >>= f)
  Action w >>= f = Action ((>>= f) <$> w)

instance (Functor m) => Alternative (WeightedListT m) where
  empty = mzero
  (<|>) = mplus

instance (Functor m) => MonadFail (WeightedListT m) where
  fail _ = Fail

instance (Functor m) => MonadPlus (WeightedListT m) where
  mzero = Fail
  Fail `mplus` m = m
  Yield x m `mplus` n = Yield x (m `mplus` n)
  Action w `mplus` m = Action (flip mplus m <$> w)
  Weight w m `mplus` Action a = Action (mplus (Weight w m) <$> a)
  Weight w m `mplus` Fail = Weight w m
  Weight w m `mplus` Yield x n = Yield x (Weight w m `mplus` n)
  Weight w m `mplus` Weight w' n =
    case compare w w' of
      LT -> Weight w (m `mplus` Weight (minusNatural w' w) n)
      EQ -> Weight w (m `mplus` n)
      GT -> Weight w' (Weight (minusNatural w w') m `mplus` n)

instance (Functor m, Foldable m) => Foldable (WeightedListT m) where
  foldMap _ Fail = mempty
  foldMap f (Yield a ms) = f a `mappend` foldMap f ms
  foldMap f (Weight _ w) = foldMap f w
  foldMap f (Action w) = fold (foldMap f <$> w)

instance (Traversable m) => Traversable (WeightedListT m) where
  sequenceA Fail = pure Fail
  sequenceA (Yield x w) = Yield <$> x <*> sequenceA w
  sequenceA (Weight a w) = Weight a <$> sequenceA w
  sequenceA (Action w) = Action <$> sequenceA (sequenceA <$> w)

toList :: Monad m => WeightedListT m a -> m [a]
toList Fail = pure []
toList (Yield x ms) = (x :) <$> toList ms
toList (Weight _ ms) = toList ms
toList (Action a) = toList =<< a

firstThat :: Monad m => (a -> Bool) -> WeightedListT m a -> m (Maybe a)
firstThat _ Fail = pure Nothing
firstThat p (Yield x ms) =
  if p x then pure (Just x) else firstThat p ms
firstThat p (Weight _ ms) =
  firstThat p ms
firstThat p (Action a) =
  firstThat p =<< a

instance MonadTrans WeightedListT where
  lift x = Action (return <$> x)

instance (MonadIO m) => MonadIO (WeightedListT m) where
  liftIO x = Action (return <$> liftIO x)

instance (MonadState s m) => MonadState s (WeightedListT m) where
  get = lift get
  put = lift . put

instance (MonadReader r m) => MonadReader r (WeightedListT m) where
  ask = lift ask
  local f = mapWeightedListT (local f)

{-
instance forall s w m. (MonadWriter s m) => MonadWriter s (WeightedListT m) where
  tell = lift . tell
  listen = go mempty
    where
      go :: s -> WeightedListT m a -> WeightedListT m (a, s)
      go _acc Fail = Fail
      go acc (Yield x m) = Yield (x, acc) (go acc m)
      go acc (Weight w m) = Weight w (go acc m)
      go acc (Action a) = Action $ do
        (w, r) <- listen a
        pure $ go (acc <> r) w
  pass = ???
-}

instance (MonadError e m) => MonadError e (WeightedListT m) where
  throwError = lift . throwError
  catchError Fail _h = Fail
  catchError (Yield x m) h = Yield x (catchError m h)
  catchError (Weight w m) h = Weight w (catchError m h)
  catchError (Action a) h = Action $ a `catchError` (return . h)

class Functor m => MonadWeightedList m where
  weight :: Natural -> m a -> m a

instance Functor m => MonadWeightedList (WeightedListT m) where
  weight = Weight

instance MonadWeightedList m => MonadWeightedList (ReaderT r m) where
  weight n (ReaderT r) = ReaderT (weight n . r)

instance MonadWeightedList m => MonadWeightedList (ExceptT r m) where
  weight n (ExceptT r) = ExceptT (weight n r)

instance MonadWeightedList m => MonadWeightedList (StateT r m) where
  weight n (StateT r) = StateT (weight n . r)

instance MonadWeightedList m => MonadWeightedList (WriterT r m) where
  weight n (WriterT r) = WriterT (weight n r)
