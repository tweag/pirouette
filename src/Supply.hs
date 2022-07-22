{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnboxedTuples #-}

module Supply
  ( Supply,
    newSupply,
    newSupplyIO,
    runSupply,
    supplyValue,
    split,
    split2,
  )
where

import Control.Monad.ST
import Data.STRef
import GHC.Base (MutVar#, State#, newMutVar#, noDuplicate#)
import GHC.Exts (atomicModifyMutVar#)
import GHC.ST (ST (..), STRep)

-- This module is based on a few sources from the internet, and from conversations
-- with Alexis King. Check the bottom of the file for a thorough explanation on State#
-- and the following links and papers to understand the technique.
--
-- 1. https://stackoverflow.com/questions/6311512/creating-unique-labels-in-haskell/63406066#63406066
-- 2. https://hackage.haskell.org/package/value-supply-0.6
-- 3. https://www.cambridge.org/core/services/aop-cambridge-core/content/view/763DE73EB4761FDF681A613BE0E98443/S0956796800000988a.pdf/functional_pearl_on_generating_unique_names.pdf

-- | A 'Supply' is a splitable suply of unique values of type @a@.
-- new values can be obtained with 'supplyValue', which can only be
-- called once per 'Supply'. In order to provide supplies for recursive calls,
-- you must 'split' the 'Supply' first. Failing to do so will result
-- in a runtime error.
data Supply a = forall s. Supply (UseOnce# s -> a) (UseOnce# s)

instance Functor Supply where
  fmap f (Supply g u) = Supply (f . g) u

-- | This is the recomended wrapper to run a supply if all you care about is
-- the uniqueness of supplied values, provided by the 'Eq' class. More general
-- supplies can be created with 'newSupply' and 'newSupplyIO'.
runSupply :: (forall a. (Eq a, Show a) => Supply a -> b) -> b
runSupply f = f (runST (newSupply (0 :: Int) succ))

-- | Creates a new supply with a given seed and /next/ function.
-- Being on the 'ST' monad is crucial, since it stops GHC from
-- transforming a call @f (newSupply z s) (newSupply z s)@ into
-- @let x = newSupply z s in f x x@, since that cause the same
-- supply to be reused. The /next/ function must be cycle-free
-- for everything to work as expected.
newSupply :: forall s a. a -> (a -> a) -> ST s (Supply a)
newSupply start next = do
  -- A supply, internally, will be a STRef that is updated
  -- every time the function @g@ is called.
  r <- newSTRef start
  ST $ use# (Supply $ asUseOnce# (unST $ nextValue r))
  where
    nextValue :: STRef s a -> ST s a
    nextValue r =
      let upd a = let b = next a in seq b (b, a)
       in atomicModifySTRef r upd

-- | Just like 'newSupply', but returns the supply in the @IO@ monad instead.
newSupplyIO :: a -> (a -> a) -> IO (Supply a)
newSupplyIO start next = stToIO (newSupply start next)

-- | Consumes a supply, retrieving a new value. It is guaranteed that
-- if @s@ is a supply obtained from transitively splitting some
-- other supply @s0@, that is, @s \in transitiveReflexiveClosure split s0@,
-- then @supplyValue s@ is different from @supplyValue s'@ where
-- @s' \in transitiveReflexiveClosure split s0 - { s }@.
supplyValue :: Supply a -> a
supplyValue (Supply g u) = g u

-- | Splits a supply into an infinite list of supplies, this function needs to
-- be used in conjunction with @take n@ or explicitely pattern matched with
-- an underscore in the tail:
--
-- > case split s of
-- >   s1 : s2 : _ -> ...
split :: Supply a -> [Supply a]
split s0 =
  let !(s1, s2) = split2 s0
   in s1 : split s2

-- | Splits a supply in two further supplies.
split2 :: Supply a -> (Supply a, Supply a)
split2 (Supply g u) =
  let !(# u1, u2 #) = split2# u
   in (Supply g u1, Supply g u2)

-- Local Definitions

atomicModifySTRef :: STRef s a -> (a -> (a, b)) -> ST s b
atomicModifySTRef r f = do
  x <- readSTRef r
  let !(x', y) = f x
  writeSTRef r x'
  return y

unST :: ST s a -> STRep s a
unST (ST act) = act

-- * Single-use values

-- | 'UseOnce#' values can be thought of as unique values.
-- They can be used to make sure that we call 'use#' only once per
-- allocated 'UseOnce#', but we can also 'split#' a unused value into
-- two. For more information on what this is and why it works, check the commentary
-- at the end of this file.
type UseOnce# s = String -> State# s

-- | Splits an unused value into two unused values.
split2# :: UseOnce# s -> (# UseOnce# s, UseOnce# s #)
split2# h =
  let !s = h "split2"
      !(# s', h1 #) = dispense# s
      (# _, h2 #) = dispense# s'
   in (# h1, h2 #)

-- | Uses a /use-once/ resource in this current state thread; that
--  resource will not be able to be used again.
use# :: (UseOnce# s -> a) -> State# s -> (# State# s, a #)
use# g s =
  let !(# s', h #) = dispense# s
      -- this is where the "use" really happens: dispense# returns a UseOnce#
      -- and h will be @expire# s' r@, which when given an argument will modify
      -- the underlying MutVar placing a call to error inside, which
      -- stop anyone from ever "using" it again during runtime.
      !r = g h
   in (# s', r #)

-- | Create a new /use-once/ resource in this state thread. The trick
--  is in returning a closure that when given an argument, will update
--  an internal 'MutVar#' setting it to error whenever it is /used/.
dispense# :: State# s -> (# State# s, UseOnce# s #)
dispense# s0 =
  let !(# s1, r #) = newMutVar# () s0
   in (# s1, expire# s1 r #)

-- | Expires a resource, by pushing @error@ into the 'MutVar#'. If that
-- particular mutvar is ever used again, that error will be evaluated.
expire# :: State# s -> MutVar# s () -> String -> State# s
expire# s0 r name =
  let !(# s1, () #) = atomicModifyMutVar# r (error (name ++ " expired"),) s0
   in s1

-- | Given an action that produces an @a@ from a given @State# s@, run
--  it on the @State# s@ given by the 'UseOnce#', once applied to a constant
--  string. The 'noDuplicate#' is important: it ensures that two threads will never
--  attempt to evaluate that thunk at the same time, which could end up calling 'dispence#' twice.
asUseOnce# :: (State# s -> (# State# s, a #)) -> UseOnce# s -> a
asUseOnce# act h = let (# _, t #) = act (noDuplicate# (h "asUseOnce#")) in t

-- I finally understood how this module worked after a great explanation from
-- Alexis King on what is @State#@. I will just quote her explanation verbatim here.
-- Alongside the commentary on the different functions in here, it should
-- give you enough to start playing around with the implementation of this module.
--
-- Open quotes:
--
-- Haskell-the-language is semantically completely pure, which is to say @f x@ always reduces to the
-- same value given the same argument @x@. This is true even for functions that return @IO@:
-- a function @f :: Int -> IO Int@ always returns the same @IO Int@ value. It just so happens
-- that when the runtime executes the resulting IO action, it may do impure things.
--
-- GHC exploits this property during optimization. If you have an expression
-- @foo (bar 1) (bar 1)@, GHC will rewrite it to @let x = bar 1 in foo x x@. Similarly, if you have an expression:
--
-- > \x -> foo x (bar 1)
--
-- Then GHC will rewrite it to
--
-- > let y = bar y
-- > in \x -> foo x y
--
-- To avoid re-evaluating @bar 1@ every time the function is applied.
--
-- But @IO@ has to actually be implemented somehow, and this raises the question of what representation
-- can allow GHC to compile @IO@ code efficiently without it ever accidentally rearranging code in a
-- way that changes semantics. For example, suppose we have a primitive for generating a random
-- integer called @randInt :: IO Int@. We certainly can’t use @newtype IO a = IO a@ because then GHC could rewrite
--
-- > randInt >>= \x -> randInt >>= \y -> pure (x + y)
--
-- to @let { x = randInt; y = randInt } in x + y@ and then to @let x = randInt in x + x@, which is not what we want.
--
-- @IO@ needs to be implemented internally /as a function/ in order to have any hope of success,
-- because a function can at least produce different results when given different inputs.
-- We could therefore imagine IO being implemented this way:
--
-- > newtype IO a = IO (Unique -> (a, Unique))
--
-- The @Monad@ instance here is literally just the usual one for @State Unique@. Now we can have
-- a @randInt# :: Unique -> (Int, Unique)@ primop that generates a random @Int@, and there’s no problem
-- as long as GHC doesn’t know anything about the implementation of @randInt#@! For all it knows,
-- every use of @randInt#@ could return a different @Unique@, and therefore if we have
--
-- > \u1 -> let (x, u2) = readInt# u1
-- >            (y, u3) = readInt# u2
-- >        in (x + y, u3)
--
-- then GHC can’t assume @randInt# u1@ and @randInt# u2@ return the same value because they’re applied
-- to different arguments! So everything works out as we want. The only problem with this is
-- that now we have all these dummy @Unique@ values floating around, even though in reality, primops
-- like @randInt#@ don’t care about the @Unique@ values at all (they could always just return their
-- argument and the strategy would still work fine). So GHC’s trick is to represent @IO@ this way:
--
-- > newtype State# s = State# (# #) -- the unboxed unit
-- > newtype IO a = IO (State# RealWorld -> (# a, State# RealWorld #))
--
-- This isn’t literally the way it’s defined, because in order for the trick to work, the GHC optimizer
-- has to be clueless to the fact that @State#@ doesn’t actually hold any information (and therefore
-- all @State#@ values are equivalent), but it’s pretty close. The idea is just that @State#@ looks just
-- like threading around a @Unique@ everywhere to the typechecker and optimizer, but to the code
-- generator and runtime, it actually has no representation at all—it’s totally free.
--
-- So @State#@ is really just a performance trick to implement @IO@ without having to pass around
-- dummy pointers. If you want, you can pretend there’s a definition somewhere @type State# s = Unique@,
-- and everything will pretty much work the same way.
