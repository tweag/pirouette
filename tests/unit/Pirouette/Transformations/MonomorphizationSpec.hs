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

sampleProgram :: Program Ex
sampleProgram =
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
                (\(x : a) (xs2 : List a) . mplus a (fold m xs2))
                zero
          )

fun intMonoid : Monoid Integer
     = Mon @Integer 0 (\(x : Integer) (y : Integer) . x + y)

fun myList : List Integer
      = Cons @Integer 3 (Cons @Integer 12 (Nil @Integer))

fun main : Integer = fold @Integer intMonoid myList
|]

sampleUDefs :: PrtUnorderedDefs Ex
sampleUDefs = uncurry PrtUnorderedDefs sampleProgram

withSampleUDefs ::
  (forall m. PirouetteReadDefs Ex m => m Assertion) ->
  Assertion
withSampleUDefs m =
  case mockPrt (runReaderT m sampleUDefs) of
    Left err -> assertFailure err
    Right t -> t

tests :: [TestTree]
tests =
  [ -- We expect that 'Monoid' is a higher-order definition and is picked by findPolyHOFDefs
    testCase "findPolyHOFDefs picks 'Monoid'" $
      assertBool "not there" $ "Monoid" `M.member` findPolyHOFDefs (prtUODecls sampleUDefs),
    -- In order to get the transitive closure of all the definitions that use ho-defs,
    -- we rely on 'hofsClosure':
    testCase "hofsClosure picks the expected defs" $
      let ds = prtUODecls sampleUDefs
       in M.keys (hofsClosure ds (findPolyHOFDefs ds)) @?= sort ["Mon", "Monoid", "fold", "match_Monoid"],
    -- Now we make sure that the function specialization requests are working as we expect:
    testGroup
      "specFunApp"
      [ testCase "specFunApp (id @Bool True) == (id@Bool True, [SpecRequest ...])" $
           runWriter (specFunApp (M.singleton "id" idDef) [term| id @Bool True |])
                @?= ([term| id!TyBool True |], [SpecRequest idDef [[ty| Bool |]]]),
        testCase "specFunApp (const @Integer @Bool 42 False) == (const!Integer!Bool 42 False, [SpecRequest ...])" $
           runWriter (specFunApp (M.singleton "const" constDef) [term| const @Integer @Bool 42 True |])
                @?= ([term| const!TyInteger!TyBool 42 True |], [SpecRequest constDef [[ty| Integer |], [ty| Bool |]]])
      ],
    testGroup
      "executeSpecRequest"
      [ testCase "specTyApp (Either3 Bool Integer) fixes type-variables and produces correct constructors" $
          executeSpecRequest (head $ snd $ runWriter $ specTyApp (M.singleton "Either3" either3Def) [ty| Either3 Bool Integer |])
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
    [ ( "Either3!TyBool!TyInteger",
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
      ("match_Either3!TyBool!TyInteger", DDestructor "Either3!TyBool!TyInteger"),
      ("Left!TyBool!TyInteger", DConstructor 0 "Either3!TyBool!TyInteger"),
      ("Mid!TyBool!TyInteger", DConstructor 1 "Either3!TyBool!TyInteger"),
      ("Right!TyBool!TyInteger", DConstructor 2 "Either3!TyBool!TyInteger")
    ]