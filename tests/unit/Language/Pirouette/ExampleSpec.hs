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
      canParseType [ty| \x : * . x |]
      canParseType [ty| forall f : * -> * . \(x : *) (y : *) . f x -> f y |]
      canParseType [ty| One (Two Three) (Four Five) Six Seven |]
      canParseType [ty| forall a : * . forall b : * . a -> b -> a |]
      canParseType [ty| Integer -> (forall a : * . Integer) |]
      canParseType [ty| forall a : * . a -> forall b : * . a -> Integer |]
      canParseType [ty| forall a : * . a -> forall b : (* -> *) . Integer -> b a -> Integer |],
    testCase "Type binders with or without parenthesis" $ do
      let t1 = [ty| \(x : *) (y : *) (z : *) . F x y |]
          t2 = [ty| \(x : *) . \(y : *) . \(z : *) . F x y |]
       in (t1 :: Type Ex) @?= t2,
    testGroup
      "Can parse terms"
      [ testCase "Example 1" $
          canParseTerm [term| if @Integer 3 < 5 then 42 + 1 else 0 |],
        testCase "Example 2" $
          canParseTerm [term| /\ (f : * -> *) (x : *) . \k : f (Either x Bool) . fmap whatever k |]
      ],
    testCase "Can parse program" $
      canParseProgram
        [prog|
          data Either a b = Left : Either a b | Right : Either a b
        |],
    testGroup
      "New syntax for function declaration"
      [ testGroup
          "Can parse function declarations using the new syntax"
          [ testCase "Declaration of all parameters" $
              canParseDefinition
                [funDecl|
          foo : Bool -> Integer -> Integer
          foo b i = if @Integer b then (i + 1) else (i - 1)
        |],
            testCase "Partially point-free" $
              canParseDefinition
                [funDecl|
          foo : Bool -> Integer -> Integer
          foo b = \ (i : Integer) . if @Integer b then (i + 1) else (i - 1)
        |],
            testCase "With a type parameter with explicit kind" $
              canParseDefinition
                [funDecl|
          foo : forall (a : *) . List a -> Maybe a
          foo @a l = if @(Maybe (List a)) empty l then Nothing @a else Just @a l
        |],
            testCase "With a type parameter with omitted kind" $
              canParseDefinition
                [funDecl|
          foo : forall a . List a -> Maybe a
          foo @a l = if @(Maybe (List a)) empty l then Nothing @a else Just @a l
        |],
            testCase "With a type parameters and naming the type variable differently in the body" $
              canParseDefinition
                [funDecl|
          foo : forall a . List a -> Maybe a
          foo @b l = if @(Maybe (List b)) empty l then Nothing @b else Just @b l
        |],
            testCase "With type parameters and naming it the same in the body" $
              canParseDefinition
                [funDecl|
          foo : forall a . List a -> (forall b . List b -> Either b a)
          foo @a l1 @b l2 =
            if @(Either (List a) (List b)) empty l1
            then Left @b l2
            else Right @a l1
        |],
            testCase "With type parameters and naming them in the body" $
              canParseDefinition
                [funDecl|
          foo : forall a . List a -> (forall b . List b -> Either b a)
          foo @c l1 @d l2 =
            if @(Either (List c) (List d)) empty l1
            then Left @c l2
            else Right @d l1
        |],
            testCase "With type parameters where there is name shadowing" $
              canParseDefinition
                [funDecl|
          foo : forall a . List a -> (forall a . List a -> Maybe a)
          foo @c l1 @d l2 =
            if @(Maybe (List d)) empty l1
            then Nothing
            else Just @d l2
        |]
          ],
        testGroup
          "Parsed function declarations match expectations"
          [ testCase "With type parameters and conflict-prone type parameter names in the body" $
              assertRightBody
                (Abs (Ann "b") KStar (Lam (Ann "l") (TyApp (Free (TySig "List")) [TyApp (Bound (Ann "b") 0) []]) (Abs (Ann "a") KStar (Lam (Ann "e") (TyApp (Free (TySig "Either")) [TyApp (Bound (Ann "a") 0) [], TyApp (Bound (Ann "b") 1) []]) (App (Free (TermSig "undefined")) [])))))
                [funDecl|
          foo : forall a . List a -> (forall b . Either b a -> Int)
          foo @b l @a e = undefined
        |]
          ]
      ],
    testGroup
      "Case constructs"
      [ testCase "With one pattern (pair)" $
          canParseDefinition
            [funDecl|
          fst : forall a . forall b . Pair a b -> a
          fst @a @b p =
            case @(Pair a b) @a p of {
              Pair x y -> x
            }
              |],
        testCase "With two patterns (lists)" $
          canParseDefinition
            [funDecl|
          head : forall a . List a -> Maybe a
          head @a l =
            case @(List a) @(Maybe a) l of {
              Cons x xs -> undefined ;
              Nil -> undefined
            }|],
        testCase "With two patterns (lists) and a catch all" $
          canParseDefinition
            [funDecl|
          head : forall a . List a -> Maybe a
          head @a l =
            case @(List a) @(Maybe a) l of {
              Cons x xs -> undefined ;
              _ -> undefined
            }|],
        testCase "Nested patterns (list of pairs) with catch-alls" $
          canParseDefinition
            [funDecl|
          fsthead : forall a . forall b . List (Pair a b) -> Maybe a
          fsthead @a @b l =
            case @(List (Pair a b)) @(Maybe a) l of {
              Cons (Pair x y) _ -> Just @a x ;
              _ -> Nothing @a
            }|]
      ],
    testGroup
      "Line folding and whitespaces"
      [ testCase "Two one-liner functions" $
          canParseProgram
            [prog|
          inc : Integer -> Integer
          inc x = x + 1
          dec : Integer -> Integer
          dec x = x - 1
              |],
        testCase "Multiline functions with comments, empty lines, and trailing spaces" $
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
      ],
    testGroup
      "Explicit and implicit kinds"
      [ testCase "Explicit kinds in datatype declaration" $
          canParseProgram
            [prog|
                data MaybePair (a : *) (b : *)
                  = Nothing : MaybePair a b
                  | JustPair : a -> b -> MaybePair a b
              |],
        testCase "Implicit kinds in datatype declaration" $
          canParseProgram
            [prog|
                data MaybePair a b
                  = Nothing : MaybePair a b
                  | JustPair : a -> b -> MaybePair a b
              |],
        testCase "Explicit kinds in function declaration" $
          canParseProgram
            [prog|
                foo : forall (a : * -> * -> *) (b : *) (c : *) . a b c
                foo @a @b @c = bottom @(a b c)
              |],
        testCase "Implicit kinds in function declaration" $
          canParseProgram
            [prog|
                foo : forall (a : * -> * -> *) b c . a b c
                foo @a @b @c = bottom @(a b c)
              |]
      ]
  ]

assertRightBody :: Term Ex -> Definition Ex -> Assertion
assertRightBody targetBody (DFunDef (FunDef _ body _)) =
  when (body /= targetBody) $
    assertFailure ("Body mismatches expectation: " <> show body)
