{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

module Pirouette.Transformations.DefunctionalizationSpec (tests) where

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Map as Map
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Transformations
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.Monomorphization
import Test.Tasty
import Test.Tasty.HUnit

tests :: [TestTree]
tests =
  [ testGroup "Monomorphic" defuncTestsMono,
    testGroup "Polymorphic" defuncTestsPoly
  ]

uDefs :: Program Ex -> PrtUnorderedDefs Ex
uDefs = uncurry PrtUnorderedDefs

-- * Monomorphic Tests

defuncTestsMono :: [TestTree]
defuncTestsMono =
  [ testCase "add and apply, monomorphic" $
      defunctionalize (uDefs addAndApply) `equalModuloDestructors` uDefs addAndApplyDefunc,
    testCase "add and const, monomorphic" $
      defunctionalize (uDefs addConst) `equalModuloDestructors` uDefs addConstDefunc,
    testCase "data type, monomorphic, free variables" $
      defunctionalize (uDefs dataType) `equalModuloDestructors` uDefs dataTypeDefunc
  ]
  where
    -- We're testing equality of definitions except for destructors
    equalModuloDestructors :: PrtUnorderedDefs Ex -> PrtUnorderedDefs Ex -> Assertion
    equalModuloDestructors p1 p2 = do
      let decls1 = Map.filter (not . isDestructor) $ prtUODecls p1
          decls2 = Map.filter (not . isDestructor) $ prtUODecls p2
          msg =
            unlines
              [ "## decls1: ",
                renderSingleLineStr (pretty decls1),
                "",
                "## decls2: ",
                renderSingleLineStr (pretty decls2)
              ]
      assertBool msg (decls1 == decls2)
      prtUOMainTerm p1 @=? prtUOMainTerm p2
      where
        isDestructor DDestructor {} = True
        isDestructor _ = False

addAndApply, addAndApplyDefunc :: Program Ex
(addAndApply, addAndApplyDefunc) =
  ( [prog|
fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun apply : (Integer -> Integer) -> Integer -> Integer
    = \(f : Integer -> Integer) (x : Integer) . f x

fun two : Integer
    = apply (add 1) 1

fun main : Integer = 42
|],
    [prog|
fun nonrec _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(cls : Closure!!TyInteger_TyInteger) .
      match_Closure!!TyInteger_TyInteger cls @(Integer -> Integer) (\(η : Integer) . add 1 η)

data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Closure!!TyInteger_TyInteger

fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun apply : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(f : Closure!!TyInteger_TyInteger) (x : Integer) . _Apply!!TyInteger_TyInteger f x

fun two : Integer
    = apply Closure!!TyInteger_TyInteger_ctor_0 1

fun main : Integer = 42
|]
  )

addConst, addConstDefunc :: Program Ex
(addConst, addConstDefunc) =
  ( [prog|
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
   = apply (apply (add 2)) 2

fun main : Integer = 42
|],
    [prog|
data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_1 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_2 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_3 : Closure!!TyInteger_TyInteger

fun nonrec _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(cls : Closure!!TyInteger_TyInteger) .
      match_Closure!!TyInteger_TyInteger cls @(Integer -> Integer)
        (\(η : Integer) . add 2 η)
        (\(η : Integer) . apply Closure!!TyInteger_TyInteger_ctor_0 η)
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
|]
  )

dataType, dataTypeDefunc :: Program Ex
(dataType, dataTypeDefunc) =
  ( [prog|
data IntHomo
  = IntHomoC : (Integer -> Integer) -> IntHomo

fun applyIntHomoToOne : IntHomo -> Integer
  = \(h : IntHomo) . match_IntHomo h @Integer (\(f : Integer -> Integer) . f 1)

fun main : Integer -> Integer = \(k : Integer) . applyIntHomoToOne (IntHomoC (\(x : Integer) . x + k))
|],
    [prog|
data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Integer -> Closure!!TyInteger_TyInteger

data IntHomo
  = IntHomoC : Closure!!TyInteger_TyInteger -> IntHomo

fun nonrec _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
    = \(cls : Closure!!TyInteger_TyInteger) .
      match_Closure!!TyInteger_TyInteger cls @(Integer -> Integer) (\(k : Integer) (η : Integer) . η + k)

fun applyIntHomoToOne : IntHomo -> Integer
  = \(h : IntHomo) . match_IntHomo h @Integer (\(f : Closure!!TyInteger_TyInteger) . _Apply!!TyInteger_TyInteger f 1)

fun main : Integer -> Integer = \(k : Integer) . applyIntHomoToOne (IntHomoC (Closure!!TyInteger_TyInteger_ctor_0 k))
|]
  )

-- * Polymorphic Tests

defuncTestsPoly :: [TestTree]
defuncTestsPoly =
  [ testCase "Nested closures are generated" $
      case monoDefunc (uDefs bug) of
        PrtOrderedDefs !x !y !z -> return ()
  ]
  where
    monoDefunc :: PrtUnorderedDefs Ex -> PrtOrderedDefs Ex
    monoDefunc = elimEvenOddMutRec . defunctionalize . monomorphize


bug :: Program Ex
bug =
  [prog|
fun appOne : all (k : Type) . (k -> Bool) -> k -> Bool
  = /\(k : Type) . \(predi : k -> Bool)(m : k) . predi m

fun appSym : all (k : Type) . (k -> k -> Bool) -> k -> Bool
  = /\(k : Type) . \(predi : k -> k -> Bool)(m : k) . appOne @k (predi m) m

fun eqInt : Integer -> Integer -> Bool
  = \(x : Integer) (y : Integer) . x == y

fun main : Bool = appSym @Integer eqInt 2
|]
