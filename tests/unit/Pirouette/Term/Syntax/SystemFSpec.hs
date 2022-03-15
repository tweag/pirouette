{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
module Pirouette.Term.Syntax.SystemFSpec (tests) where

import Pirouette.Term.Syntax.SystemF hiding (tyApp)

import Data.List (groupBy, transpose)
import Control.Arrow (first)

import Language.Pirouette.Example
import           Control.Monad
import           Test.Tasty
import           Test.Tasty.HUnit

sameTy :: Type Ex -> Type Ex -> Assertion
sameTy = (@?=)

tests :: TestTree
tests = testGroup "SystemF"
  [ testGroup "Unit Tests:"
    [ testCase "type-level application" $
        sameTy [ty| \f :: Type -> Type . (\x :: Type . f x) (\w :: Type . w) |]
               [ty| \f :: Type -> Type . f (\w :: Type . w) |]
    ]
  ]
