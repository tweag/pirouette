{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Pirouette.Transformations.DCESpec (tests) where

import Control.Monad.Identity
import Control.Monad.Reader
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
  ]

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