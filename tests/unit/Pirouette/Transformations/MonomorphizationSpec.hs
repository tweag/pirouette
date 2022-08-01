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
-- Here we're overloading the constructor name on purpose, to make
-- sure monomorphization understands that it must monomorphize
-- both the type and the constructor
data Monoid a
  = Monoid : a -> (a -> a -> a) -> Monoid a

data List a
  = Cons : a -> List a -> List a
  | Nil : List a

-- Here's a tricky one! It's an indirect need for monomorphizing:
-- If we don't monomorphize @Ind@, defunctionalization will not
-- be able to properly generate closures for the arguments.
data Indirect a
  = Ind : Maybe (a -> a) -> Indirect a

data Maybe a
  = Just : a -> Maybe a
  | Nothing : Maybe a

foldMon : forall a . Monoid a -> List (Maybe a) -> Maybe a
foldMon @a m xs =
      match_Monoid @(Maybe a) (maybeMonoid @a m) @(Maybe a)
        (\(zero : Maybe a) (mplus : Maybe a -> Maybe a -> Maybe a)
          . match_List @(Maybe a) xs @(Maybe a)
              (\(x : Maybe a) (xs2 : List (Maybe a)) . mplus x (foldMon @a m xs2))
              zero
        )

maybeMonoid : forall a . Monoid a -> Monoid (Maybe a)
maybeMonoid @a m =
     match_Monoid @a m @(Monoid (Maybe a))
     (\(z : a) (f : a -> a -> a)
     . Monoid @(Maybe a) (Nothing @a)
        (\(ma : Maybe a) (mb : Maybe a)
        . match_Maybe @a ma @(Maybe a)
            (\(x : a) . match_Maybe @a mb @(Maybe a)
              (\(y : a) . Just @a (f x y))
              (Just @a x))
            mb))

intMonoid : Monoid Integer
intMonoid = Monoid @Integer 0 (\(x : Integer) (y : Integer) . x + y)

main : Maybe Integer
main = foldMon @Integer intMonoid (Nil @(Maybe Integer))
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
              [ (TypeNamespace, "Indirect"),
                (TypeNamespace, "Monoid"),
                (TypeNamespace, "List"),
                (TypeNamespace, "Maybe"),
                (TermNamespace, "match_Indirect"),
                (TermNamespace, "Ind"),
                (TermNamespace, "Monoid"),
                (TermNamespace, "match_Monoid"),
                (TermNamespace, "foldMon"),
                (TermNamespace, "match_List"),
                (TermNamespace, "Cons"),
                (TermNamespace, "Nil"),
                (TermNamespace, "match_Maybe"),
                (TermNamespace, "maybeMonoid"),
                (TermNamespace, "Nothing"),
                (TermNamespace, "Just")
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
          runWriter
            ( specFunApp
                (M.singleton (TermNamespace, "id") $ Just idDef)
                [term| id @Bool True |]
            )
            @?= ([term| id<TyBool> True |], [SpecRequest "id" idDef [[ty| Bool |]]]),
        testCase "specFunApp (const @Integer @Bool 42 False) == (const<Integer$Bool> 42 False, [SpecRequest ...])" $
          runWriter
            ( specFunApp
                (M.singleton (TermNamespace, "const") $ Just constDef)
                [term| const @Integer @Bool 42 True |]
            )
            @?= ([term| const<TyInteger$TyBool> 42 True |], [SpecRequest "const" constDef [[ty| Integer |], [ty| Bool |]]])
      ],
    testGroup
      "executeSpecRequest"
      [ testCase "specTyApp (Either3 Bool Integer) fixes type-variables and produces correct constructors" $
          executeSpecRequest
            ( head $
                snd $
                  runWriter $
                    specTyApp
                      (M.singleton (TypeNamespace, "Either3") $ Just either3Def)
                      [ty| Either3 Bool Integer |]
            )
            @?= either3Def_Bool_Integer_decls
      ]
  ]

constDef :: FunOrTypeDef Ex
constDef = SystF.TermArg $ FunDef Rec funterm funtype
  where
    funtype = [ty| forall (a : *) (b : *) . a -> b -> a |]
    funterm = [term| /\ (a : *) (b : *) . \ (x : a) (y : b) . x |]

idDef :: FunOrTypeDef Ex
idDef = SystF.TermArg $ FunDef Rec funterm funtype
  where
    funtype = [ty| forall a : * . a -> a |]
    funterm = [term| /\ a : * . \ x : a . x |]

either3Def :: FunOrTypeDef Ex
either3Def =
  SystF.TyArg $
    Datatype
      { kind = SystF.KTo SystF.KStar (SystF.KTo SystF.KStar (SystF.KTo SystF.KStar SystF.KStar)),
        typeVariables = [("a", SystF.KStar), ("b", SystF.KStar), ("c", SystF.KStar)],
        destructor = "match_Either3",
        constructors =
          [ ("Left", [ty| forall (a : *) (b : *) (c : *) . a -> Either3 a b c |]),
            ("Mid", [ty| forall (a : *) (b : *) (c : *) . b -> Either3 a b c |]),
            ("Right", [ty| forall (a : *) (b : *) (c : *) . c -> Either3 a b c |])
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
                [ ("Left<TyBool$TyInteger>", [ty| forall (c : *) . Bool -> Either3<TyBool$TyInteger> c |]),
                  ("Mid<TyBool$TyInteger>", [ty| forall (c : *) . Integer -> Either3<TyBool$TyInteger> c |]),
                  ("Right<TyBool$TyInteger>", [ty| forall (c : *) . c -> Either3<TyBool$TyInteger> c |])
                ]
            }
      ),
      ((TermNamespace, "match_Either3<TyBool$TyInteger>"), DDestructor "Either3<TyBool$TyInteger>"),
      ((TermNamespace, "Left<TyBool$TyInteger>"), DConstructor 0 "Either3<TyBool$TyInteger>"),
      ((TermNamespace, "Mid<TyBool$TyInteger>"), DConstructor 1 "Either3<TyBool$TyInteger>"),
      ((TermNamespace, "Right<TyBool$TyInteger>"), DConstructor 2 "Either3<TyBool$TyInteger>")
    ]
