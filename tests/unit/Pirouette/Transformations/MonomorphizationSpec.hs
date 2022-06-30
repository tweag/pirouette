{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Transformations.MonomorphizationSpec (tests) where

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

sampleUDefs :: PrtUnorderedDefs Ex
sampleUDefs =
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
                (\(x : a) (xs2 : List a) . mplus x (fold @a m xs2))
                zero
          )

fun maybeSum : all (x : Type) . Maybe x -> Maybe x -> Maybe x
  = /\ (x : Type) . \(mx : Maybe x)(my : Maybe x)
  . match_Maybe @x mx @(Maybe x)
      my
      (\(jx : x) . Just @x jx)

fun intMonoid : Monoid Integer
     = Mon @Integer 0 (\(x : Integer) (y : Integer) . x + y)

fun myList : List Integer
      = Cons @Integer 3 (Cons @Integer 12 (Nil @Integer))

fun main : Integer = fold @Integer intMonoid myList
|]

withSampleUDefs ::
  (forall m. PirouetteReadDefs Ex m => m Assertion) ->
  Assertion
withSampleUDefs m = runReader m sampleUDefs

tests :: [TestTree]
tests =
  [ -- We expect that 'Monoid' is a higher-order definition and is picked by findPolyHOFDefs
    testCase "findPolyHOFDefs picks 'Monoid'" $
      assertBool "not there" $ (TypeNamespace, "Monoid") `M.member` findPolyHOFDefs (prtUODecls sampleUDefs),
    -- In order to get the transitive closure of all the definitions that use ho-defs,
    -- we rely on 'hofsClosure'.
    testCase "hofsClosure picks the expected defs" $
      let ds = prtUODecls sampleUDefs
       in sort (map snd (M.keys (hofsClosure ds (findPolyHOFDefs ds))))
            @?= sort ["Mon", "Monoid", "fold", "match_Monoid"],
    -- Now we make sure that the function specialization requests are working as we expect:
    testGroup
      "specFunApp"
      [ testCase "specFunApp (id @Bool True) == (id@Bool True, [SpecRequest ...])" $
          runWriter (specFunApp (M.singleton (TermNamespace, "id") idDef) [term| id @Bool True |])
            @?= ([term| id!TyBool True |], [SpecRequest idDef [[ty| Bool |]]]),
        testCase "specFunApp (const @Integer @Bool 42 False) == (const!Integer!Bool 42 False, [SpecRequest ...])" $
          runWriter (specFunApp (M.singleton (TermNamespace, "const") constDef) [term| const @Integer @Bool 42 True |])
            @?= ([term| const!TyInteger!TyBool 42 True |], [SpecRequest constDef [[ty| Integer |], [ty| Bool |]]])
      ],
    testGroup
      "executeSpecRequest"
      [ testCase "specTyApp (Either3 Bool Integer) fixes type-variables and produces correct constructors" $
          executeSpecRequest (head $ snd $ runWriter $ specTyApp (M.singleton (TypeNamespace, "Either3") either3Def) [ty| Either3 Bool Integer |])
            @?= either3Def_Bool_Integer_decls
      ]
  ]

constDef :: HofDef Ex
constDef = HofDef "const" $ HDBFun $ FunDef Rec funterm funtype
  where
    funtype = [ty| all (a : Type) (b : Type) . a -> b -> a |]
    funterm = [term| /\ (a : Type) (b : Type) . \ (x : a) (y : b) . x |]

idDef :: HofDef Ex
idDef = HofDef "id" $ HDBFun $ FunDef Rec funterm funtype
  where
    funtype = [ty| all a : Type . a -> a |]
    funterm = [term| /\ a : Type . \ x : a . x |]

either3Def :: HofDef Ex
either3Def =
  HofDef "Either3" $
    HDBType $
      Datatype
        { kind = SystF.KTo SystF.KStar (SystF.KTo SystF.KStar (SystF.KTo SystF.KStar SystF.KStar)),
          typeVariables = [("a", SystF.KStar), ("b", SystF.KStar), ("c", SystF.KStar)],
          destructor = "match_Either3",
          constructors =
            [ ("Left", [ty| all (a : Type) (b : Type) (c : Type) . a -> Either3 a b c |]),
              ("Mid", [ty| all (a : Type) (b : Type) (c : Type) . b -> Either3 a b c |]),
              ("Right", [ty| all (a : Type) (b : Type) (c : Type) . c -> Either3 a b c |])
            ]
        }

either3Def_Bool_Integer_decls :: Decls Ex
either3Def_Bool_Integer_decls =
  M.fromList
    [ ( (TypeNamespace, "Either3!TyBool!TyInteger"),
        DTypeDef
          Datatype
            { kind = SystF.KTo SystF.KStar SystF.KStar,
              typeVariables = [("c", SystF.KStar)],
              destructor = "match_Either3!TyBool!TyInteger",
              constructors =
                [ ("Left!TyBool!TyInteger", [ty| all (c : Type) . Bool -> Either3!TyBool!TyInteger c |]),
                  ("Mid!TyBool!TyInteger", [ty| all (c : Type) . Integer -> Either3!TyBool!TyInteger c |]),
                  ("Right!TyBool!TyInteger", [ty| all (c : Type) . c -> Either3!TyBool!TyInteger c |])
                ]
            }
      ),
      ((TermNamespace, "match_Either3!TyBool!TyInteger"), DDestructor "Either3!TyBool!TyInteger"),
      ((TermNamespace, "Left!TyBool!TyInteger"), DConstructor 0 "Either3!TyBool!TyInteger"),
      ((TermNamespace, "Mid!TyBool!TyInteger"), DConstructor 1 "Either3!TyBool!TyInteger"),
      ((TermNamespace, "Right!TyBool!TyInteger"), DConstructor 2 "Either3!TyBool!TyInteger")
    ]
