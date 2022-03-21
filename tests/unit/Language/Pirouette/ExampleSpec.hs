{-# LANGUAGE QuasiQuotes #-}

module Language.Pirouette.ExampleSpec (tests) where

import Language.Pirouette.Example
import Pirouette.Term.Syntax.Base
import Test.Tasty
import Test.Tasty.HUnit

canParseTerm :: Term Ex -> Assertion
canParseTerm _ = return ()

canParseType :: Type Ex -> Assertion
canParseType _ = return ()

canParseProgram :: Program Ex -> Assertion
canParseProgram _ = return ()

tests :: [TestTree]
tests =
  [ testGroup
      "Can parse types"
      [ testCase "Example 1" $ canParseType [ty| \x : Type . x |],
        testCase "Example 2" $ canParseType [ty| all f : Type -> Type . \(x : Type) (y : Type) . f x -> f y |],
        testCase "Example 3" $ canParseType [ty| One (Two Three) (Four Five) Six Seven |],
        testCase "Example 4" $
          let t1 = [ty| \(x : Type) (y : Type) . F x y |]
              t2 = [ty| \(x : Type) . \(y : Type) . F x y |]
           in (t1 :: Type Ex) @?= t2
      ],
    testGroup
      "Can parse terms"
      [ testCase "Example 1" $
          canParseTerm [term| if 3 < 5 then 42 + 1 else 0 |],
        testCase "Example 2" $
          canParseTerm [term| /\ (f : Type -> Type) (x : Type) . \k : f (Either x Bool) . fmap whatever k |]
      ],
    testCase "Can parse program" $
      canParseProgram
        [prog|
          data Either (a : Type) (b : Type) = Left : Either a b | Right : Either a b
          fun main : Integer = 42
        |]
  ]
