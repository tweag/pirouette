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

beforePrenex, afterPrenex :: Program Ex
beforePrenex =
  [prog|
fun example : all a : Type . a -> all b : Type . b -> a
  = /\ a : Type . \(x : a) . /\ b : Type . \(y : b) . a

fun main : Integer = example @Integer 3 @Integer 4
|]

afterPrenex =
  [prog|
fun example : all a : Type . all b : Type . a -> b -> a
  = /\ a : Type . /\ b : Type . \(x : a) (y : b) . a

fun main : Integer = example @Integer @Integer 3 4
|]

uDefs :: Program Ex -> PrtUnorderedDefs Ex
uDefs = uncurry PrtUnorderedDefs

tests :: [TestTree]
tests =
  [ testCase "prenex example" $
      prenex (uDefs beforePrenex) @=? uDefs afterPrenex
  ]