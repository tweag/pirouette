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
import Data.Foldable (asum)
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
runTreeT = go (\s x -> pure (Done s x))
  where
    go :: forall b r. 
          (state -> b -> m (Tree tag state r))  -- continuation
       -> TreeT tag state m b -> state
       -> m (Tree tag state r)
    -- the simple ones
    go _ EmptyT _ = pure Stop
    go k (LiftT action) s = k s =<< action
    go k GetT s = k s s
    go k (PutT newS) _ = k newS ()
    -- splitting choices
    go k (SplitT choices) s = do
      branches <- forM choices \(tg, nxt) -> Branch tg <$> go k nxt s
      pure (Split s branches)
    -- the fmap (for performance win, since we can do better than the liftM from Control.Monad)
    go k (FmapT g x) s = go (\s' x' -> k s' (g x')) x s
    -- the ap (for performance win, since we can do better than the ap from Control.Monad)
    go k (ApT fs xs) s =
      go (\s1 f -> go (\s2 x -> k s2 (f x)) xs s1) fs s
    -- the bind
    go k (BindT this nxt) s =
      go (\s1 x -> go k (nxt x) s1) this s

-- | Specialized version of the runner for the 'Identity' monad.
runTreeI :: forall tag state a. 
            TreeT tag state Identity a -> state -> Tree tag state a
runTreeI = go Done
  where
    go :: forall b r. 
          (state -> b -> Tree tag state r)  -- continuation
       -> TreeT tag state Identity b -> state
       -> Tree tag state r
    -- the simple ones
    go _ EmptyT _ = Stop
    go k (LiftT (Identity action)) s = k s action
    go k GetT s = k s s
    go k (PutT newS) _ = k newS ()
    -- splitting choices
    go k (SplitT choices) s =
      let branches = flip map choices \(tg, nxt) -> Branch tg (go k nxt s)
      in Split s branches
    -- the fmap (for performance win, since we can do better than the liftM from Control.Monad)
    go k (FmapT g x) s = 
      go (\s' x' -> k s' (g x')) x s
    -- the ap (for performance win, since we can do better than the ap from Control.Monad)
    go k (ApT fs xs) s =
      go (\s1 f -> go (\s2 x -> k s2 (f x)) xs s1) fs s
    -- the bind
    go k (BindT this nxt) s = 
      go (\s1 x -> go k (nxt x) s1) this s

-- | Specialized version to check a property.
runTreeAny :: forall tag state f a r.
              Alternative f =>
              (a -> f r) ->
              TreeT tag state Identity a -> state -> f r
runTreeAny predicate = go (const predicate)
  where
    go :: (state -> b -> f q)
       -> TreeT tag state Identity b
       -> state -> f q
    go _ EmptyT _ = empty
    go p (LiftT (Identity action)) s = p s action
    go p GetT s = p s s
    go p (PutT newS) _ = p newS ()
    go p (SplitT choices) s =
      asum $ flip map choices \(_tg, nxt) -> go p nxt s
    go p (FmapT g x) s = 
      go (\s' x' -> p s' (g x')) x s
    go p (ApT fs xs) s =
      go (\s1 f -> go (\s2 x -> p s2 (f x)) xs s1) fs s
    go p (BindT this nxt) s = 
      go (\s1 x -> go p (nxt x) s1) this s

{-# SPECIALIZE runTreeAny :: forall tag state a r.
                             (a -> Maybe r) ->
                             TreeT tag state Identity a -> state -> Maybe r #-}

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