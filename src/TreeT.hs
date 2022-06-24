{-# language BlockArguments #-}
{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language FunctionalDependencies #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language UndecidableInstances #-}

module TreeT where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.Writer
import Control.Parallel.Strategies
import Data.Sequence (Seq)
import qualified Data.Sequence as S

-- These are the result data types

data Tree tag state a
  = Stop
  | Done  state a
  | Split state [Branch tag state a]
  deriving (Eq, Show, Functor, Foldable)

data Branch tag state a
  = Branch { tag :: tag, next :: Tree tag state a }
  deriving (Eq, Show, Functor, Foldable)

-- | Traverse the tree breadth-first.
levels :: Tree tag state a -> Seq a
levels t = go (S.singleton t)
  where
    go S.Empty = S.empty
    go (v S.:<| xs) =
      case v of
        Stop -> go xs
        Done _ x -> x S.:<| go xs
        Split _ bs -> go (xs S.>< S.fromList (map next bs))

treeFind :: Alternative f => (a -> Bool) -> Tree tag state a -> f a
treeFind p = go
  where
    go Stop = empty
    go (Done _ x) = x <$ guard (p x)
    go (Split _ bs) = goBranches bs
    goBranches [] = empty
    goBranches (Branch _ nxt : rest) =
      go nxt <|> goBranches rest
{-# SPECIALIZE treeFind :: (a -> Bool) -> Tree tag state a -> Maybe a #-}

-- | Runs a 'TreeT' computation, resulting in a 'Tree'.
runTreeT :: forall tag state m a. Monad m
         => TreeT tag state m a -> state -> m (Tree tag state a)
runTreeT = go id
  where
    go :: forall b r. (b -> r) -- when we fmap we build a continuation here
       -> TreeT tag state m b -> state
       -> m (Tree tag state r)
    -- the simple ones
    go _ EmptyT _ = pure Stop
    go f (LiftT action) s = Done s . f <$> action
    go f GetT s = pure (Done s (f s))
    go f (PutT newS) _ = pure (Done newS (f ()))
    -- splitting choices
    go f (SplitT choices) s = do
      branches <- forM choices \(tg, nxt) -> Branch tg <$> go f nxt s
      pure (Split s branches)
    -- the fmap (for performance win, since we can do better than the liftM from Control.Monad)
    go f (FmapT g x) s = go (f . g) x s
    -- the ap (for performance win, since we can do better than the ap from Control.Monad)
    go f (ApT fs xs) s = do
      f' <- go id fs s
      goAp f'
      where
        goAp Stop = pure Stop
        goAp (Done s' gs) =
          fmap (f . gs) <$> go id xs s'
        goAp (Split s' bs) =
          Split s' <$> forM bs \(Branch tg t) ->
            Branch tg <$> goAp t
    -- the bind
    go f (BindT this nxt) s = do
      this' <- go id this s
      goBind this'
      where
        goBind Stop = pure Stop
        goBind (Done s' x) = go f (nxt x) s'
        goBind (Split s' bs) = Split s' <$> forM bs \(Branch tg t) -> Branch tg <$> goBind t

-- | Specialized version of the runner for the 'Identity' monad.
runTreeI :: forall tag state a. 
            (forall x. Strategy x -> Strategy [x]) ->
            TreeT tag state Identity a -> state -> Tree tag state a
runTreeI strat = go id
  where
    go :: forall b r. (b -> r) -- when we fmap we build a continuation here
       -> TreeT tag state Identity b -> state
       -> Tree tag state r
    -- the simple ones
    go _ EmptyT _ = Stop
    go f (LiftT (Identity action)) s = Done s (f action)
    go f GetT s = Done s (f s)
    go f (PutT newS) _ = Done newS (f ())
    -- splitting choices
    go f (SplitT choices) s =
      let branches = withStrategy (strat rseq) $ 
                       flip map choices \(tg, nxt) ->
                        Branch tg (go f nxt s)
      in Split s branches
    -- the fmap (for performance win, since we can do better than the liftM from Control.Monad)
    go f (FmapT g x) s = go (f . g) x s
    -- the ap (for performance win, since we can do better than the ap from Control.Monad)
    go f (ApT fs xs) s = goAp (go id fs s)
      where
        goAp Stop = Stop
        goAp (Done s' gs) = fmap (f . gs) (go id xs s')
        goAp (Split s' bs) =
          let branches = withStrategy (strat rseq) $ 
                           flip map bs \(Branch tg t) -> 
                             Branch tg (goAp t)
          in Split s' branches
    -- the bind
    go f (BindT this nxt) s = goBind (go id this s)
      where
        goBind Stop = Stop
        goBind (Done s' x) = go f (nxt x) s'
        goBind (Split s' bs) = 
          let branches = withStrategy (strat rseq) $
                           flip map bs \(Branch tg t) -> 
                             Branch tg (goBind t)
          in Split s' branches 

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
  FmapT  :: (a -> b) -> TreeT tag state m a -> TreeT tag state m b
  ApT    :: TreeT tag state m (a -> b) -> TreeT tag state m a -> TreeT tag state m b
  BindT  :: TreeT tag state m a -> (a -> TreeT tag state m b) -> TreeT tag state m b
  -- Different branches
  SplitT :: [(tag, TreeT tag state m a)] -> TreeT tag state m a
  -- MonadState
  GetT   :: TreeT tag state m state
  PutT   :: state -> TreeT tag state m ()

hoistTreeT :: forall tag state m n a. Functor n
           => (forall x. m x -> n x)
           -> TreeT tag state m a -> TreeT tag state n a
hoistTreeT f = go
  where
    go :: forall b. TreeT tag state m b -> TreeT tag state n b
    go EmptyT = EmptyT
    go (LiftT x) = LiftT (f x)
    go (FmapT g x) = FmapT g (go x)
    go (ApT x y) = ApT (go x) (go y)
    go (BindT x nxt) = BindT (go x) (go . nxt)
    go (SplitT bs) = SplitT [(tg, go b) | (tg, b) <- bs]
    go GetT = GetT
    go (PutT x) = PutT x

instance Applicative m => Functor (TreeT tag state m) where
  fmap = FmapT

instance Applicative m => Applicative (TreeT tag state m) where
  pure  = return
  (<*>) = ApT

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