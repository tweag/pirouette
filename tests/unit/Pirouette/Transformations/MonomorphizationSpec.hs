{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Transformations.MonomorphizationSpec (tests) where

import Control.Monad.Reader
import Data.List (sort)
import qualified Data.Map as M
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Transformations.Monomorphization
import Pirouette.Transformations.Utils
import Test.Tasty
import Test.Tasty.HUnit

sampleProgram :: Program Ex
sampleProgram =
  [prog|
data Maybe (a : Type)
  = Nothing : Maybe a
  | Just : a -> Maybe a

data Monoid (a : Type)
  = Mon : a -> (a -> a -> a) -> Monoid a

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
     = Mon @Integer 0 (\(x : Integer) (y : Integer) . x + y)

fun myList : List Integer
      = Cons @Integer 3 (Cons @Integer 12 (Nil @Integer))

fun main : Integer = fold @Integer intMonoid myList
|]

sampleUDefs :: PrtUnorderedDefs Ex
sampleUDefs = uncurry PrtUnorderedDefs sampleProgram

withSampleUDefs ::
  (forall m. PirouetteReadDefs Ex m => m Assertion) ->
  Assertion
withSampleUDefs m =
  case mockPrt (runReaderT m sampleUDefs) of
    Left err -> assertFailure err
    Right t -> t

tests :: [TestTree]
tests =
  [ testCase "Monoid is a higher-order type" $
      withSampleUDefs $ do
        monoidDef <- prtTypeDefOf "Monoid"
        return $
          assertBool "no HO constructor" $
            (hasHOFuns . snd) `any` constructors monoidDef,
    testCase "findPolyHOFDefs picks 'Monoid'" $
      assertBool "not there" $ "Monoid" `M.member` findPolyHOFDefs (prtUODecls sampleUDefs),
    testCase "hofsClosure picks the expected defs" $
      let ds = prtUODecls sampleUDefs
       in M.keys (hofsClosure ds (findPolyHOFDefs ds)) @?= ["Mon", "Monoid", "fold", "match_Monoid"]
  ]
