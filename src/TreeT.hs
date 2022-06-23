{-# language BlockArguments #-}
{-# language DeriveFunctor #-}
{-# language FunctionalDependencies #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language UndecidableInstances #-}

module TreeT where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.Writer

-- These are the result data types

data Tree tag state a
  = Stop
  | Done  state a
  | Split state [Branch tag state a]
  deriving (Eq, Show, Functor)

data Branch tag state a
  = Branch { tag :: tag, next :: Tree tag state a }
  deriving (Eq, Show, Functor)

-- | Runs a 'TreeT' computation, resulting in a 'Tree'.
runTreeT :: Monad m => TreeT tag state m a -> state -> m (Tree tag state a)
-- the simple ones
runTreeT EmptyT _ = pure Stop
runTreeT (LiftT action) s = Done s <$> action
runTreeT GetT s = pure (Done s s)
runTreeT (PutT newS) _ = pure (Done newS ())
-- splitting choices
runTreeT (SplitT choices) s = do
  branches <- forM choices \(tg, nxt) -> Branch tg <$> runTreeT nxt s
  pure (Split s branches)
-- the bind
runTreeT (BindT this nxt) s = do
  this' <- runTreeT this s
  go this'
  where
    go Stop = pure Stop
    go (Done s' x) = runTreeT (nxt x) s'
    go (Split s' bs) = Split s' <$> forM bs \(Branch tg t) -> Branch tg <$> go t

-- | Defines a class of monad which support pruning and branching.
class Monad m => MonadTree tag m | m -> tag where
  stop :: m a
  branch :: [(tag, m a)] -> m a

-- | The monad which defines actions which keep a 'state',
-- and also may prune and branch.
data TreeT tag state m a where
  -- Monad
  EmptyT :: TreeT tag state m a
  LiftT  :: m a -> TreeT tag state m a
  BindT  :: TreeT tag state m a -> (a -> TreeT tag state m b) -> TreeT tag state m b
  -- Different branches
  SplitT :: [(tag, TreeT tag state m a)] -> TreeT tag state m a
  -- MonadState
  GetT   :: TreeT tag state m state
  PutT   :: state -> TreeT tag state m ()

hoistTreeT :: forall tag state m n a. Functor n
         => (forall x. m x -> n x) -> TreeT tag state m a -> TreeT tag state n a
hoistTreeT f = go
  where
    go :: forall b. TreeT tag state m b -> TreeT tag state n b
    go EmptyT = EmptyT
    go (LiftT x) = LiftT (f x)
    go (BindT x nxt) = BindT (go x) (go . nxt)
    go (SplitT bs) = SplitT [(tg, go b) | (tg, b) <- bs]
    go GetT = GetT
    go (PutT x) = PutT x

instance Applicative m => Functor (TreeT tag state m) where
  fmap = liftM

instance Applicative m => Applicative (TreeT tag state m) where
  pure  = return
  (<*>) = ap

instance Applicative m => Monad (TreeT tag state m) where
  return = LiftT . pure
  (>>=)  = BindT

instance MonadTrans (TreeT tag state) where
  lift = LiftT

instance Applicative m => MonadTree tag (TreeT tag state m) where
  stop = EmptyT
  branch = SplitT

instance Applicative m => MonadState state (TreeT tag state m) where
  get = GetT
  put = PutT

instance MonadReader r m => MonadReader r (TreeT tag state m) where
  ask = lift ask
  local f = hoistTreeT (local f)

instance MonadTree tag m => MonadTree tag (ReaderT r m) where
  stop = lift stop
  branch bs = ReaderT $ \r -> branch [(tg, runReaderT b r) | (tg, b) <- bs]

instance (MonadTree tag m, Monoid w) => MonadTree tag (WriterT w m) where
  stop = lift stop
  branch bs = WriterT $ branch [(tg, runWriterT b) | (tg, b) <- bs]