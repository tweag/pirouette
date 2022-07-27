{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Pirouette.Transformations.DCESpec (tests) where

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Generics.Uniplate.Data
import Data.Map as Map
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.TypeChecker
import Pirouette.Transformations.DCE
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

tests :: [TestTree]
tests =
  [ testGroup "Finding dead constructors" findDeadCtorsTest
  , testGroup "Executing constructor removal" removeCtorsTest
  , testGroup "Everything together: eliminating dead constructors" removeDeadCtorsTest
  , testGroup "Unused fields" unusedFieldsTest
  ]

unusedFieldsTest :: [TestTree]
unusedFieldsTest =
  [ testCase "detected correctly" $ do
      unusedFields src1 (getType src1 "Ty1") 0 @?= []
      unusedFields src1 (getType src1 "Ty1") 1 @?= [2]
      unusedFields srcPoly (getType srcPoly "Extended") 0 @?= [1]
      unusedFields srcPoly (getType srcPoly "Extended") 1 @?= []
      unusedFields srcPoly (getType srcPoly "Extended") 2 @?= []
  , testCase "removed correctly, given their list" $ do
      transformBi (updateDtor @Ex "match_Ty1" 1 [0, 2]) (getFunBody src1 "foo") @?= getFunBody resFoo1 "foo"
      transformBi (updateDtor @Ex "match_Ty1" 1 [2])    (getFunBody src1 "foo") @?= getFunBody res1    "foo"
  , testCase "detected and removed correctly" $
      removeDeadFields src1 @?= res1
  ]
  where
    getType prog name = case prtUODecls prog Map.! (TypeNamespace, name) of
                             DTypeDef td -> td

    getFunBody prog name = case prtUODecls prog Map.! (TermNamespace, name) of
                                DFunDef fd -> funBody fd
                                _ -> error "not a function"

    src1 :: PrtUnorderedDefs Ex
    src1 = [prog|
data Ty1
  = Ty1C1 : Integer -> Ty1
  | Ty2C1 : Integer -> Ty1 -> Integer -> Ty1

fun foo : Ty1 -> Integer
  = \(t : Ty1).
    match_Ty1 t @Integer
      (\(a : Integer). 1)
      (\(a : Integer) (b : Ty1) (c : Integer). foo b)

fun bar : Ty1 -> Integer
  = \(t : Ty1).
    match_Ty1 t @Integer
      (\(a : Integer). a)
      (\(a : Integer) (b : Ty1) (c : Integer). a + foo b)
|]

    resFoo1 :: PrtUnorderedDefs Ex
    resFoo1 = [prog|
data Ty1
  = Ty1C1 : Integer -> Ty1
  | Ty2C1 : Ty1 -> Ty1

fun foo : Ty1 -> Integer
  = \(t : Ty1).
    match_Ty1 t @Integer
      (\(a : Integer). 1)
      (\(b : Ty1). foo b)
|]

    res1 :: PrtUnorderedDefs Ex
    res1 = [prog|
data Ty1
  = Ty1C1 : Integer -> Ty1
  | Ty2C1 : Integer -> Ty1 -> Ty1

fun foo : Ty1 -> Integer
  = \(t : Ty1).
    match_Ty1 t @Integer
      (\(a : Integer). 1)
      (\(a : Integer) (b : Ty1). foo b)

fun bar : Ty1 -> Integer
  = \(t : Ty1).
    match_Ty1 t @Integer
      (\(a : Integer). a)
      (\(a : Integer) (b : Ty1). a + foo b)
|]

    srcPoly :: PrtUnorderedDefs Ex
    srcPoly = [prog|
data Extended (a : Type)
  = Finite : a -> Extended a
  | NegInf : Extended a
  | PosInf : Extended a
|]

findDeadCtorsTest :: [TestTree]
findDeadCtorsTest =
  [ testCase "Unused type has all its ctors unused" $
      findDeadCtors s1 @=? [CtorRemoveInfo "Ty" "TyC2" 1 "match_Ty" , CtorRemoveInfo "Ty" "TyC1" 0 "match_Ty"]
  , testCase "Used type is handled correctly" $
      findDeadCtors s2 @=? [CtorRemoveInfo "Ty" "TyC1" 0 "match_Ty"]
  ]
  where
    s1, s2 :: PrtUnorderedDefs Ex
    s1 = [prog|
data Ty
  = TyC1 : Ty
  | TyC2 : Integer -> Ty
|]

    s2 = [prog|
data Ty
  = TyC1 : Ty
  | TyC2 : Integer -> Ty

fun foo : Integer -> Ty
  = \(n : Integer) . TyC2 n
|]

prettyEqual :: PrtUnorderedDefs Ex -> PrtUnorderedDefs Ex -> Assertion
prettyEqual result expected = assertBool msg (result == expected)
  where
    msg =
      unlines
        [ "Expected:",
          renderSingleLineStr (pretty $ prtUODecls expected),
          "",
          "but got:",
          "",
          renderSingleLineStr (pretty $ prtUODecls result)
        ]

removeCtorsTest :: [TestTree]
removeCtorsTest =
  [ testCase "removes a given constructor" $
      removeCtor (CtorRemoveInfo "Ty1" "Ty1C2" 1 "match_Ty1") s1 `prettyEqual` r1
  ]
  where
    s1 = [prog|
data Ty1
    = Ty1C1 : Ty1
    | Ty1C2 : Integer -> Ty1
    | Ty1C3 : Integer -> Integer -> Ty1

data Ty2
    = Ty2C1 : Ty2
    | Ty2C2 : Integer -> Ty2
    | Ty2C3 : Integer -> Integer -> Ty2

fun foo1 : Ty1 -> Integer
    = \(t : Ty1) .
      match_Ty1 t @Integer
        1
        (\(a : Integer) . 2)
        (\(a : Integer) (b : Integer) . 3)

fun foo2 : Ty2 -> Integer
    = \(t : Ty2) .
      match_Ty2 t @Integer
        1
        (\(a : Integer) . 2)
        (\(a : Integer) (b : Integer) . 3)
|]
    r1 = [prog|
data Ty1
    = Ty1C1 : Ty1
    | Ty1C3 : Integer -> Integer -> Ty1

data Ty2
    = Ty2C1 : Ty2
    | Ty2C2 : Integer -> Ty2
    | Ty2C3 : Integer -> Integer -> Ty2

fun foo1 : Ty1 -> Integer
    = \(t : Ty1) .
      match_Ty1 t @Integer
        1
        (\(a : Integer) (b : Integer) . 3)

fun foo2 : Ty2 -> Integer
    = \(t : Ty2) .
      match_Ty2 t @Integer
        1
        (\(a : Integer) . 2)
        (\(a : Integer) (b : Integer) . 3)
|]

removeDeadCtorsTest :: [TestTree]
removeDeadCtorsTest =
  [ testCase "respects the whitelist when removing" $
      removeDeadCtors (RemoveDeadCtorsOpts $ Map.fromList [("Ty1", ["Ty1C1", "Ty1C3", "Ty1C4"])]) s1 `prettyEqual` r1
  , testCase "removes dead ctors, and in the right order" $
      removeDeadCtors (RemoveDeadCtorsOpts $ Map.fromList [("Ty1", ["Ty1C1", "Ty1C3", "Ty1C4"])]) s2 `prettyEqual` r2
  ]
  where
    s1 = [prog|
data Ty1
    = Ty1C1 : Ty1
    | Ty1C2 : Integer -> Ty1
    | Ty1C3 : Integer -> Integer -> Ty1
    | Ty1C4 : Integer -> Integer -> Integer -> Ty1

data Ty2
    = Ty2C1 : Ty2
    | Ty2C2 : Integer -> Ty2
    | Ty2C3 : Integer -> Integer -> Ty2
|]
    r1 = [prog|
data Ty1
    = Ty1C2 : Integer -> Ty1

data Ty2
    = Ty2C1 : Ty2
    | Ty2C2 : Integer -> Ty2
    | Ty2C3 : Integer -> Integer -> Ty2
|]

    s2 = [prog|
data Ty1
    = Ty1C1 : Ty1
    | Ty1C2 : Integer -> Ty1
    | Ty1C3 : Integer -> Integer -> Ty1
    | Ty1C4 : Integer -> Integer -> Integer -> Ty1
    | Ty1C5 : Integer -> Integer -> Integer -> Integer -> Ty1

data Ty2
    = Ty2C1 : Ty2
    | Ty2C2 : Integer -> Ty2
    | Ty2C3 : Integer -> Integer -> Ty2

fun matcher1 : Ty1 -> Integer
    = \(t : Ty1) .
      match_Ty1 t @Integer
        1
        (\(a : Integer) . 2)
        (\(a : Integer) (b : Integer) . 3)
        (\(a : Integer) (b : Integer) (c : Integer) . 4)
        (\(a : Integer) (b : Integer) (c : Integer) (d : Integer) . 5)

fun matcher2 : Ty2 -> Integer
    = \(t : Ty2) .
      match_Ty2 t @Integer
        1
        (\(a : Integer) . 2)
        (\(a : Integer) (b : Integer) . 3)

fun id1 : Ty1 -> Ty1
    = \(t : Ty1) . t

fun mk11 : Ty1
    = id1 Ty1C1

fun mk13 : Ty1
    = id1 (Ty1C3 6 42)


fun id2 : Ty2 -> Ty2
    = \(t : Ty2) . t

fun mk21 : Ty2
    = id2 Ty2C1

fun mk22 : Ty2
    = id2 (Ty2C2 6)

fun mk23 : Ty2
    = id2 (Ty2C3 6 42)
|]
    r2 = [prog|
data Ty1
    = Ty1C1 : Ty1
    | Ty1C2 : Integer -> Ty1
    | Ty1C3 : Integer -> Integer -> Ty1
    | Ty1C5 : Integer -> Integer -> Integer -> Integer -> Ty1

data Ty2
    = Ty2C1 : Ty2
    | Ty2C2 : Integer -> Ty2
    | Ty2C3 : Integer -> Integer -> Ty2

fun matcher1 : Ty1 -> Integer
    = \(t : Ty1) .
      match_Ty1 t @Integer
        1
        (\(a : Integer) . 2)
        (\(a : Integer) (b : Integer) . 3)
        (\(a : Integer) (b : Integer) (c : Integer) (d : Integer) . 5)

fun matcher2 : Ty2 -> Integer
    = \(t : Ty2) .
      match_Ty2 t @Integer
        1
        (\(a : Integer) . 2)
        (\(a : Integer) (b : Integer) . 3)

fun id1 : Ty1 -> Ty1
    = \(t : Ty1) . t

fun mk11 : Ty1
    = id1 Ty1C1

fun mk13 : Ty1
    = id1 (Ty1C3 6 42)


fun id2 : Ty2 -> Ty2
    = \(t : Ty2) . t

fun mk21 : Ty2
    = id2 Ty2C1

fun mk22 : Ty2
    = id2 (Ty2C2 6)

fun mk23 : Ty2
    = id2 (Ty2C3 6 42)
|]
