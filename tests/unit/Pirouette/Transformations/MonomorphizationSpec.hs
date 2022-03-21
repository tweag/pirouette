{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
module Pirouette.Transformations.MonomorphizationSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Transformations.Monomorphization
import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as M
import Data.List (sort)

sampleProgram :: Program Ex
sampleProgram =
  [prog|
data Maybe (a : Type)
  = Nothing : Maybe a
  | Just : a -> Maybe a

data Monoid (a : Type)
  = Monoid : a -> (a -> a -> a) -> Monoid a

data List (a : Type)
  = Cons : a -> List a -> List a
  | Nil : List a

fun fold : all a : Type . Monoid a -> List a -> a
      = /\ a : Type . \(m : Monoid a) (xs : List a)
      . match_Monoid @a m @a
          (\(zero : a) (mplus : a -> a -> a)
            . match_List @a xs @a
                (\(x : a) (xs2 : List a) . mplus a (fold m xs2))
                zero
          )

fun intMonoid : Monoid Integer
     = Monoid @Integer 0 (\(x : Integer) (y : Integer) . x + y)

fun myList : List Integer
      = Cons @Integer 3 (Cons @Integer 12 (Nil @Integer))

fun main : Integer = fold @Integer intMonoid myList
|]

sampleUDefs :: PrtUnorderedDefs Ex
sampleUDefs = uncurry PrtUnorderedDefs sampleProgram

tests :: [TestTree]
tests =
  [ testCase "findPolyHOFDefs works" $
      assertBool "Something should have changed" (monomorphize sampleUDefs /= sampleUDefs)
  ]
