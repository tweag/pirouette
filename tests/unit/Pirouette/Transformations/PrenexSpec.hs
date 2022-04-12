{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Pirouette.Transformations.PrenexSpec (tests) where

import Control.Monad.Reader
import Control.Monad.Writer
import Data.List (sort)
import qualified Data.Map as M
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Monomorphization
import Pirouette.Transformations.Utils
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit
import Pirouette.Transformations.Prenex

beforePrenex1, afterPrenex1 :: Program Ex
(beforePrenex1, afterPrenex1) =
  ([prog|
fun example : all a : Type . a -> all b : Type . b -> a
  = /\ a : Type . \(x : a) . /\ b : Type . \(y : b) . x

fun main : Integer = example @Integer 3 @Integer 4
|], [prog|
fun example : all a : Type . all b : Type . a -> b -> a
  = /\ a : Type . /\ b : Type . \(x : a) (y : b) . x

fun main : Integer = example @Integer @Integer 3 4
|])

beforePrenex2, afterPrenex2 :: Program Ex
(beforePrenex2, afterPrenex2) =
  ([prog|
fun f : all a : Type . a -> all b : Type . b -> a
  = /\ a : Type . \(x : a) . /\ b : Type . \(y : b) . x
fun g : all a : Type . all b : Type . a -> b -> all c : Type . c -> a
  = /\ a : Type . /\ b : Type . \(x : a) (y : b) . /\ c : Type . \(z : c) . x

fun main : Integer = f @Integer 3 @Integer (g @Integer @Integer 4 @Integer 5)
|], [prog|
fun f : all a : Type . all b : Type . a -> b -> a
  = /\ a : Type . /\ b : Type . \(x : a) . \(y : b) . x
fun g : all a : Type . all b : Type . all c : Type . a -> b -> c -> a
  = /\ a : Type . /\ b : Type . /\ c : Type . \(x : a) (y : b) . \(z : c) . x

fun main : Integer = f @Integer @Integer 3 (g @Integer @Integer @Integer 4 5)
|])

uDefs :: Program Ex -> PrtUnorderedDefs Ex
uDefs = uncurry PrtUnorderedDefs

tests :: [TestTree]
tests =
  [ testCase "prenex example #1" $
      prenex (uDefs beforePrenex1) @=? uDefs afterPrenex1,
    testCase "prenex example #1, unchanged" $
      prenex (uDefs afterPrenex1) @=? uDefs afterPrenex1,
    testCase "prenex example #1" $
      prenex (uDefs beforePrenex2) @=? uDefs afterPrenex2,
    testCase "prenex example #2, unchanged" $
      prenex (uDefs afterPrenex2) @=? uDefs afterPrenex2
  ]
