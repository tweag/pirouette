{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Transformations.DefunctionalizationSpec (tests) where

import Control.Monad.Reader
import Data.Map as Map
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.Monomorphization
import Test.Tasty
import Test.Tasty.HUnit

uDefs :: Program Ex -> PrtUnorderedDefs Ex
uDefs = uncurry PrtUnorderedDefs

addAndApply, addAndApplyDefunc :: Program Ex
(addAndApply, addAndApplyDefunc) =
  ([prog|
fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun apply : (Integer -> Integer) -> Integer -> Integer
    = \(f : Integer -> Integer) (x : Integer) . f x

fun two : Integer 
    = apply (add 1) 1

fun main : Integer = 42
|], [prog|
fun nonrec _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(cls : Closure!!TyInteger_TyInteger) .
      match_Closure!!TyInteger_TyInteger cls @Integer (\(η : Integer) . add 1 η)

data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Closure!!TyInteger_TyInteger

fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun apply : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(f : Closure!!TyInteger_TyInteger) (x : Integer) . _Apply!!TyInteger_TyInteger f x

fun two : Integer 
    = apply Closure!!TyInteger_TyInteger_ctor_0 1

fun main : Integer = 42
|])

addConst, addConstDefunc :: Program Ex
(addConst, addConstDefunc) =
  ([prog|
fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun const : Integer -> Integer -> Integer
    = \ (x : Integer) (y : Integer) . x

fun apply : (Integer -> Integer) -> Integer -> Integer
    = \ (f : Integer -> Integer) (x : Integer) . f x

fun two : Integer 
    = apply (add 1) 1

fun three : Integer 
    = apply (const 3) 10

fun four : Integer
   = apply (apply add 2) 2

fun main : Integer = 42
|], [prog|
data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_1 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_2 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_3 : Closure!!TyInteger_TyInteger

fun _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(cls : Closure!!TyInteger_TyInteger) .
      match_Closure!!TyInteger_TyInteger cls @Integer 
        (\(η : Integer) . add 2 η) 
        (\(η : Integer) . apply Closure!!TyInteger_TyInteger_ctor_1 2 η)
        (\(η : Integer) . const 3 η)
        (\(η : Integer) . add 1 η)

fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun apply : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(f : Closure!!TyInteger_TyInteger) (x : Integer) . _Apply!!TyInteger_TyInteger f x

fun const : Integer -> Integer -> Integer
    = \ (x : Integer) (y : Integer) . x

fun four : Integer
   = apply Closure!!TyInteger_TyInteger_ctor_1 2

fun three : Integer 
    = apply Closure!!TyInteger_TyInteger_ctor_2 10

fun two : Integer 
    = apply Closure!!TyInteger_TyInteger_ctor_3 1

fun main : Integer = 42
|])

addAndApplyPoly :: Program Ex
addAndApplyPoly =
  [prog|
fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun apply : all (a : Type) (b : Type) . (a -> b) -> a -> b
    = /\ (a : Type) (b : Type) . \ (f : a -> b) (x : a) . f x

fun two : Integer 
    = apply @Integer @Integer (add 1) 1

fun main : Integer = 42
|]

addConstPoly :: Program Ex
addConstPoly =
  [prog|
fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun const : all (a : Type) (b : Type) . a -> b -> a
    = /\ (a : Type) (b : Type) . \ (x : a) (y : b) . x

fun apply : all (a : Type) (b : Type) . (a -> b) -> a -> b
    = /\ (a : Type) (b : Type) . \ (f : a -> b) (x : a) . f x

fun two : Integer 
    = apply @Integer @Integer (add 1) 1

fun three : Integer 
    = apply @Integer @Integer (const @Integer @Integer 3) 10

fun four : Integer
   = apply @Integer @Integer (apply @Integer @Integer add 2) 2

fun main : Integer = 42
|]

equalModuloDestructors :: PrtUnorderedDefs Ex -> PrtUnorderedDefs Ex -> Assertion
equalModuloDestructors p1 p2 = do
  let decls1 = Map.filter (not . isDestructor) $ prtUODecls p1
      decls2 = Map.filter (not . isDestructor) $ prtUODecls p2
  decls1 @=? decls2
  prtUOMainTerm p1 @=? prtUOMainTerm p2
  where
      isDestructor DDestructor {} = True
      isDestructor _              = False

tests :: [TestTree]
tests =
  [ testCase "add and apply, monomorphic" $
      defunctionalize (uDefs addAndApply) `equalModuloDestructors` uDefs addAndApplyDefunc,
    testCase "add and const, monomorphic" $
      defunctionalize (uDefs addConst) `equalModuloDestructors` uDefs addConstDefunc
    -- testCase "add and apply, polymorphic" $
    --   monoDefunc (uDefs addAndApplyPoly) `equalModuloDestructors` uDefs addAndApplyPoly,
    -- testCase "add and const, polymorphic" $
    --   monoDefunc (uDefs addConstPoly) `equalModuloDestructors` uDefs addConstPoly
  ]
  where
    monoDefunc :: PrtUnorderedDefs Ex -> PrtUnorderedDefs Ex
    monoDefunc = defunctionalize . monomorphize
