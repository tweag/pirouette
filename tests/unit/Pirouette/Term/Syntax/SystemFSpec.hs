{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Pirouette.Term.Syntax.SystemFSpec (tests) where

import Control.Arrow (first)
import Control.Monad
import Data.List (groupBy, transpose)
import Language.Pirouette.Example
import Pirouette.Term.Syntax.SystemF hiding (tyApp)
import Test.Tasty
import Test.Tasty.HUnit
import Pirouette.Term.Syntax.Base

-- We need to help the typechecker with some explicit types
sameTy :: Type Ex -> Type Ex -> Assertion
sameTy = (@?=)

sameTerm :: Term Ex -> Term Ex -> Assertion
sameTerm = (@?=)

tests :: [TestTree]
tests =
  [ testCase "Type-Type application" $
      sameTy
        [ty| \f : Type -> Type . (\x : Type . f x) (\w : Type . w) |]
        [ty| \f : Type -> Type . f (\w : Type . w) |],
    testCase "Term-Type application" $
      sameTerm [term| (\a : Integer . /\ r : Type . \b : r . a) 3 @Bool 4 |] [term| 3 |],
    testCase "Terms equality is alpha-equivalence" $
      sameTerm [term| \a : Integer . a |] [term| \b : Integer . b |]
  ]
