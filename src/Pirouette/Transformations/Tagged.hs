{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Transformations.Tagged where

import Data.Kind
import GHC.TypeLits

type Tags = [Type]

type Xform' :: Tags -> Tags -> Type -> Type -> Type
newtype Xform' requires provides a b = Xform (a -> b)

type Xform requires provides a = Xform' requires provides a a

type family (∪) (xs :: [a]) (ys :: [a]) :: [a] where
  '[] ∪ ys = ys
  (x ': xs) ∪ ys = x ': (xs ∪ ys)

type family Del (xs :: [a]) (d :: a) :: [a] where
  Del '[] _ = '[]
  Del (d ': xs) d = Del xs d
  Del (x ': xs) d = x ': Del xs d

type family (\\) (xs :: [a]) (ys :: [a]) :: [a] where
  xs \\ '[] = xs
  xs \\ (y ': ys) = Del xs y \\ ys

(>:>) ::
  Xform' r1 p1 a b ->
  Xform' r2 p2 b c ->
  Xform' (r1 ∪ (r2 \\ p1)) (p1 ∪ p2) a c
Xform f1 >:> Xform f2 = Xform $ f2 . f1

trivialXform :: (a -> b) -> Xform' '[] '[] a b
trivialXform = Xform

type family ReqsSatisfied (reqs :: [tag]) :: Constraint where
  ReqsSatisfied '[] = () ~ ()
  ReqsSatisfied (h ': t) = TypeError ('Text "Unsatisfied transformation pipeline dependencies: " ':<>: 'ShowType (h ': t))

xform :: (ReqsSatisfied requires) => Xform' requires provides a b -> a -> b
xform (Xform f) = f
