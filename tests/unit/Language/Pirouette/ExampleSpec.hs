{-# LANGUAGE QuasiQuotes #-}

module Language.Pirouette.ExampleSpec (tests) where

import Language.Pirouette.Example
import Pirouette.Monad (PrtUnorderedDefs (..))
import Pirouette.Term.Syntax.Base
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
      canParseType [ty| all f : Type -> Type . \(x : Type) (y : Type) . f x -> f y |]
      canParseType [ty| One (Two Three) (Four Five) Six Seven |]
      canParseType [ty| all a : Type . all b : Type . a -> b -> a |]
      canParseType [ty| Integer -> (all a : Type . Integer) |]
      canParseType [ty| all a : Type . a -> all b : Type . a -> Integer |]
      canParseType [ty| all a : Type . a -> all b : (Type -> Type) . Integer -> b a -> Integer |],
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
          data Either (a : Type) (b : Type) = Left : Either a b | Right : Either a b
          fun main : Integer = 42
        |],
    testCase "Can parse function declaration" $
      canParseDefinition
        [funDecl|
          fun foo : Bool -> Integer -> Integer = \(b : Bool) (i : Integer) . if @Integer b then (i + 1) else (i - 1)
        |],
    testGroup
      "Can parse function declarations using the new syntax"
      [ testCase "Declaration of all parameters" $
          canParseDefinition
            [newFunDecl|
          nfun foo : Bool -> Integer -> Integer !
          foo b i = if @Integer b then (i + 1) else (i - 1)
        |],
        testCase "Partially point-free" $
          canParseDefinition
            [newFunDecl|
          nfun foo : Bool -> Integer -> Integer !
          foo b = \ (i : Integer) . if @Integer b then (i + 1) else (i - 1)
        |]
      ]
  ]

-- testCase "Can parse program" $
--   canParseProgram
--     [prog|
--       data Either (a : Type) (b : Type) = Left : Either a b | Right : Either a b
--       main : Integer
--       main = 42
--     |],
-- testCase "Can parse new function decls" $
--   canParseProgram
--     [prog|
--       data Either (a : Type) (b : Type) = Left : Either a b | Right : Either a b
--       foo : Bool -> Integer -> Either Integer Integer
--       foo b i = if b then Left (i + 1) else Right (i - 1)
--     |]
