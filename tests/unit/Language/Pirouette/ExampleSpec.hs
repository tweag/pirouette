{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Language.Pirouette.ExampleSpec (tests) where

import Control.Monad (when)
import Language.Haskell.TH (Lit (IntegerL))
import Language.Pirouette.Example
import Pirouette.Monad (PrtUnorderedDefs (..))
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF
import Test.Tasty
import Test.Tasty.HUnit

canParseTerm :: Term Ex -> Assertion
canParseTerm _ = return ()

canParseType :: Type Ex -> Assertion
canParseType _ = return ()

canParseProgram :: PrtUnorderedDefs Ex -> Assertion
canParseProgram _ = return ()

canParseDefinition :: Definition Ex -> Assertion
canParseDefinition _ = return ()

tests :: [TestTree]
tests =
  [ testCase "Can parse types" $ do
      canParseType [ty| \x : Type . x |]
      canParseType [ty| forall f : Type -> Type . \(x : Type) (y : Type) . f x -> f y |]
      canParseType [ty| One (Two Three) (Four Five) Six Seven |]
      canParseType [ty| forall a : Type . forall b : Type . a -> b -> a |]
      canParseType [ty| Integer -> (forall a : Type . Integer) |]
      canParseType [ty| forall a : Type . a -> forall b : Type . a -> Integer |]
      canParseType [ty| forall a : Type . a -> forall b : (Type -> Type) . Integer -> b a -> Integer |],
    testCase "Type binders with or without parenthesis" $ do
      let t1 = [ty| \(x : Type) (y : Type) (z : Type) . F x y |]
          t2 = [ty| \(x : Type) . \(y : Type) . \(z : Type) . F x y |]
       in (t1 :: Type Ex) @?= t2,
    testGroup
      "Can parse terms"
      [ testCase "Example 1" $
          canParseTerm [term| if @Integer 3 < 5 then 42 + 1 else 0 |],
        testCase "Example 2" $
          canParseTerm [term| /\ (f : Type -> Type) (x : Type) . \k : f (Either x Bool) . fmap whatever k |]
      ],
    testCase "Can parse program" $
      canParseProgram
        [prog|
          data Either a b = Left : Either a b | Right : Either a b
        |],
    testGroup
      "Can parse function declarations"
      [ testCase "Can parse function declarations with case" $
          canParseDefinition
            [funDecl|
          rightToMaybe : forall a b . Either a b -> Maybe b
          rightToMaybe @a @b x =
            case @(Either a b) @(Maybe b) x of {
              Left _ -> Nothing ;
              Right y -> Just y
            }
          |],
        testCase "Correctly parse function with conflict-prone type parameter names in the body" $
          assertRightBody
            (Abs (Ann "b") KStar (Lam (Ann "l") (TyApp (Free (TySig "List")) [TyApp (Bound (Ann "b") 0) []]) (Abs (Ann "a") KStar (Lam (Ann "e") (TyApp (Free (TySig "Either")) [TyApp (Bound (Ann "a") 0) [], TyApp (Bound (Ann "b") 1) []]) (App (Free (TermSig "undefined")) [])))))
            [funDecl|
            foo : forall a . List a -> (forall b . Either b a -> Int)
            foo @b l @a e = undefined
            |],
        testCase "Can parse program with empty lines and comments in line-folded sections" $
          canParseProgram
            [prog|
          -- Increments a number
          inc : Integer -> Integer  
          inc x = x + 1
     
          -- Decrements a number
          dec :
               Integer -- Number to be decremented
            -> Integer
                  
          dec x =
            x - 1

              |]
      ]
  ]

assertRightBody :: Term Ex -> Definition Ex -> Assertion
assertRightBody targetBody (DFunDef (FunDef _ body _)) =
  when (body /= targetBody) $
    assertFailure ("Body mismatches expectation: " <> show body)
