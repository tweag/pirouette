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
import Data.Generics.Uniplate.Data
import Data.List (sort)
import qualified Data.Map as M
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Term.TypeChecker
import Pirouette.Transformations.Monomorphization
import Pirouette.Transformations.Utils
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

sampleUDefs :: PrtUnorderedDefs Ex
sampleUDefs =
  [prog|
data Monoid (a : Type)
  = Mon : a -> (a -> a -> a) -> Monoid a

data List (a : Type)
  = Cons : a -> List a -> List a
  | Nil : List a

-- Here's a tricky one! It's an indirect need for monomorphizing:
-- If we don't monomorphize @Ind@, defunctionalization will not
-- be able to properly generate closures for the arguments.
data Indirect (a : Type)
  = Ind : Maybe (a -> a) -> Indirect a

data Maybe (a : Type)
  = Just : a -> Maybe a
  | Nothing : Maybe a

fun foldMon : all a : Type . Monoid a -> List (Maybe a) -> Maybe a
      = /\ a : Type . \(m : Monoid a) (xs : List (Maybe a))
      . match_Monoid @(Maybe a) (maybeMonoid @a m) @(Maybe a)
          (\(zero : Maybe a) (mplus : Maybe a -> Maybe a -> Maybe a)
            . match_List @(Maybe a) xs @(Maybe a)
                (\(x : Maybe a) (xs2 : List (Maybe a)) . mplus x (foldMon @a m xs2))
                zero
          )

fun maybeMonoid : all (a : Type) . Monoid a -> Monoid (Maybe a)
     = /\(a : Type) . \(m : Monoid a)
     . match_Monoid @a m @(Monoid (Maybe a))
       (\(z : a) (f : a -> a -> a)
       . Mon @(Maybe a) (Nothing @a)
          (\(ma : Maybe a) (mb : Maybe a)
          . match_Maybe @a ma @(Maybe a)
              (\(x : a) . match_Maybe @a mb @(Maybe a)
                (\(y : a) . Just @a (f x y))
                (Just @a x))
              mb))

fun intMonoid : Monoid Integer
     = Mon @Integer 0 (\(x : Integer) (y : Integer) . x + y)

fun main : Maybe Integer = foldMon @Integer intMonoid (Nil @(Maybe Integer))
|]

castTy :: Type Ex -> Type Ex
castTy = id

mkTyApp :: Name -> Type Ex
mkTyApp n = SystF.Free (TySig n) `SystF.TyApp` []

tests :: [TestTree]
tests =
  [ testCase "genSpecName is homomorphic" $
      let tyA = castTy [ty| Maybe (Bool -> Bool) |]
          tyB = mkTyApp $ genSpecName [castTy [ty| Bool -> Bool |]] "Maybe"
       in genSpecName [tyA] "f" @?= genSpecName [tyB] "f",
    testCase "selectMonoDefs picks the expected defs" $
      let ds = selectMonoDefs sampleUDefs
       in sort (M.keys ds)
            @?= sort
              [ "Indirect",
                "Ind",
                "match_Indirect",
                "Monoid",
                "Mon",
                "match_Monoid",
                "fold",
                "List",
                "match_List",
                "Cons",
                "Nil"
              ],
    testCase "isSpecArg forbids type applications" $
      let cases :: [(Type Ex, Bool)]
          cases =
            [ ([ty| Maybe Bool |], False),
              ([ty| Integer -> Integer |], True),
              ([ty| Integer -> Integer -> Integer |], True),
              ([ty| Integer -> Maybe Integer -> Integer |], False)
            ]
       in forM_ cases $ \(ty, exp) ->
            unless (isSpecArg ty == exp) $
              assertFailure $ show $ pretty ty,
    -- Monomorphized declarations typecheck
    testCase "monomorphize sampleUDefs has no type applications" $
      let res = monomorphize sampleUDefs
       in case typeCheckDecls (prtUODecls $ monomorphize sampleUDefs) of
            Left err -> assertFailure (show $ pretty err)
            Right _ -> forM_ (M.toList $ prtUODecls res) $ \((sp, name), def) -> do
              case fromTermDef def of
                Just fd -> do
                  let nonSpecTypes :: [Type Ex]
                      nonSpecTypes = [ty | ty <- universeBi fd, not (isSpecArg ty)]
                  unless (null nonSpecTypes) $
                    assertFailure $ "Def of: " ++ show name ++ " has non specialized types: " ++ show (pretty nonSpecTypes)
                _ -> return (),
    -- Now we make sure that the function specialization requests are working as we expect:
    testGroup
      "specFunApp"
      [ testCase "specFunApp (id @Bool True) == (id@Bool True, [SpecRequest ...])" $
          runWriter (specFunApp (M.singleton "id" $ Just idDef) [term| id @Bool True |])
            @?= ([term| id<TyBool> True |], [SpecRequest "id" idDef [[ty| Bool |]]]),
        testCase "specFunApp (const @Integer @Bool 42 False) == (const<Integer$Bool> 42 False, [SpecRequest ...])" $
          runWriter (specFunApp (M.singleton "const" $ Just constDef) [term| const @Integer @Bool 42 True |])
            @?= ([term| const<TyInteger$TyBool> 42 True |], [SpecRequest "const" constDef [[ty| Integer |], [ty| Bool |]]])
      ],
    testGroup
      "executeSpecRequest"
      [ testCase "specTyApp (Either3 Bool Integer) fixes type-variables and produces correct constructors" $
          executeSpecRequest (head $ snd $ runWriter $ specTyApp (M.singleton "Either3" $ Just either3Def) [ty| Either3 Bool Integer |])
            @?= either3Def_Bool_Integer_decls
      ]
  ]

constDef :: FunOrTypeDef Ex
constDef = SystF.TermArg $ FunDef Rec funterm funtype
  where
    funtype = [ty| all (a : Type) (b : Type) . a -> b -> a |]
    funterm = [term| /\ (a : Type) (b : Type) . \ (x : a) (y : b) . x |]

idDef :: FunOrTypeDef Ex
idDef = SystF.TermArg $ FunDef Rec funterm funtype
  where
    funtype = [ty| all a : Type . a -> a |]
    funterm = [term| /\ a : Type . \ x : a . x |]

either3Def :: FunOrTypeDef Ex
either3Def =
  SystF.TyArg $
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
    [ ( (TypeNamespace, "Either3<TyBool$TyInteger>"),
        DTypeDef
          Datatype
            { kind = SystF.KTo SystF.KStar SystF.KStar,
              typeVariables = [("c", SystF.KStar)],
              destructor = "match_Either3<TyBool$TyInteger>",
              constructors =
                [ ("Left<TyBool$TyInteger>", [ty| all (c : Type) . Bool -> Either3<TyBool$TyInteger> c |]),
                  ("Mid<TyBool$TyInteger>", [ty| all (c : Type) . Integer -> Either3<TyBool$TyInteger> c |]),
                  ("Right<TyBool$TyInteger>", [ty| all (c : Type) . c -> Either3<TyBool$TyInteger> c |])
                ]
            }
      ),
      ((TermNamespace, "match_Either3<TyBool$TyInteger>"), DDestructor "Either3<TyBool$TyInteger>"),
      ((TermNamespace, "Left<TyBool$TyInteger>"), DConstructor 0 "Either3<TyBool$TyInteger>"),
      ((TermNamespace, "Mid<TyBool$TyInteger>"), DConstructor 1 "Either3<TyBool$TyInteger>"),
      ((TermNamespace, "Right<TyBool$TyInteger>"), DConstructor 2 "Either3<TyBool$TyInteger>")
    ]
