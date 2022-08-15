{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

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
import Pirouette.Transformations.Prenex
import Pirouette.Transformations.Utils
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

beforePrenex1, afterPrenex1 :: PrtUnorderedDefs Ex
(beforePrenex1, afterPrenex1) =
  ( [prog|
example : forall a . a -> forall b . b -> a
example @a x @b y = x

main : Integer
main = example @Integer 3 @Integer 4
|],
    [prog|
example : forall a . forall b . a -> b -> a
example @a @b x y = x

main : Integer
main = example @Integer @Integer 3 4
|]
  )

beforePrenex2, afterPrenex2 :: PrtUnorderedDefs Ex
(beforePrenex2, afterPrenex2) =
  ( [prog|
f : forall a . a -> forall b . b -> a
f @a x @b y = x

g : forall a . forall b . a -> b -> forall c . c -> a
g @a @b x y @c z = x

main : Integer
main = f @Integer 3 @Integer (g @Integer @Integer 4 5 @Integer 6)
|],
    [prog|
f : forall a . forall b . a -> b -> a
f @a @b x y = x

g : forall a . forall b . forall c . a -> b -> c -> a
g @a @b @c x y z = x

main : Integer
main = f @Integer @Integer 3 (g @Integer @Integer @Integer 4 5 6)
|]
  )

tests :: [TestTree]
tests =
  [ testCase "prenex example #1" $
      prenex beforePrenex1 @=? afterPrenex1,
    testCase "prenex example #1, unchanged" $
      prenex afterPrenex1 @=? afterPrenex1,
    testCase "prenex example #1" $
      prenex beforePrenex2 @=? afterPrenex2,
    testCase "prenex example #2, unchanged" $
      prenex afterPrenex2 @=? afterPrenex2
  ]
