{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Pirouette.Transformations.DefunctionalizationSpec (tests) where

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Map as Map
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.TypeChecker
import Pirouette.Transformations
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.Monomorphization
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

tests :: [TestTree]
tests =
  [ testGroup "Monomorphic" defuncTestsMono,
    testGroup "Polymorphic" defuncTestsPoly
  ]

-- * Monomorphic Tests

defuncTestsMono :: [TestTree]
defuncTestsMono =
  [ testCase "add and apply, monomorphic" $
      defunctionalize addAndApply `equalModuloDestructors` addAndApplyDefunc,
    testCase "add and const, monomorphic" $
      defunctionalize addConst `equalModuloDestructors` addConstDefunc,
    testCase "data type, monomorphic, free variables" $
      defunctionalize dataType `equalModuloDestructors` dataTypeDefunc
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
      where
        isDestructor DDestructor {} = True
        isDestructor _ = False

addAndApply, addAndApplyDefunc :: PrtUnorderedDefs Ex
(addAndApply, addAndApplyDefunc) =
  ( [prog|
fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun apply : (Integer -> Integer) -> Integer -> Integer
    = \(f : Integer -> Integer) (x : Integer) . f x

fun two : Integer
    = apply (add 1) 1
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
|]
  )

addConst, addConstDefunc :: PrtUnorderedDefs Ex
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
|]
  )

dataType, dataTypeDefunc :: PrtUnorderedDefs Ex
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
  [ testCase "Nested closures are generated and typecheck" $
      runTest nested,
    testCase "Destructors types are updated and typecheck" $
      runTest destructors,
    testCase "Indirect types are updated and typecheck" $
      runTest indirect,
    -- TODO: I'm marking this as expectFail because I'm aware our defunctionalization
    -- engine can't handle this, but we really have to address it at some point!
    expectFail $
      testCase "Mixed types are updated and typecheck" $
        runTest mixed
  ]
  where
    monoDefunc :: PrtUnorderedDefs Ex -> PrtUnorderedDefs Ex
    monoDefunc = defunctionalize . monomorphize

    runTest :: PrtUnorderedDefs Ex -> Assertion
    runTest decls0 =
      case monoDefunc decls0 of
        PrtUnorderedDefs decls -> do
          case typeCheckDecls decls of
            Left err -> assertFailure (show $ pretty err)
            Right _ -> return ()

nested :: PrtUnorderedDefs Ex
nested =
  [prog|
data Monoid (a : Type)
  = Mon : (a -> a -> a) -> a -> Monoid a

data AdditiveMonoid (a : Type)
  = AdditiveMon : (a -> a -> a) -> a -> AdditiveMonoid a

fun additiveToMonoid : all (a : Type) . AdditiveMonoid a -> Monoid a
  = /\(a : Type) . \(x : AdditiveMonoid a)
    . Mon @a (match_AdditiveMonoid @a x @(a -> a -> a) (\(f : a -> a -> a) (z : a) . f))
             (match_AdditiveMonoid @a x @a (\(f : a -> a -> a) (z : a) . z))

data List (a : Type)
  = Nil : List a
  | Cons : a -> List a -> List a

fun listMon : all (a : Type) . AdditiveMonoid (List a)
  = /\(a : Type) . AdditiveMon @(List a) (\(k : List a) (l : List a)
    . foldr @a @(List a) (Cons @a) l k) (Nil @a)

fun foldr : all (a : Type) (b : Type) . (a -> b -> b) -> b -> List a -> b
  = /\(a : Type) (b : Type) . \(f : a -> b -> b) (m : b) (xs : List a)
   . match_List @a xs @b
       m
       (\(h : a) (tl : List a) . f h (foldr @a @b f m tl))

fun foldMap : all (a : Type) (b : Type) . (a -> b) -> Monoid b -> List a -> b
  = /\(a : Type) (b : Type) . \(f : a -> b) (m : Monoid b) (xs : List a)
  . match_Monoid @b m @b
      (\ (mplus : b -> b -> b) (mzero : b)
       . foldr @a @b (\(x : a) (rest : b) . mplus (f x) rest) mzero xs
      )

fun id : all (a : Type) . a -> a
  = /\(a : Type) . \(x : a) . x

fun concat : all (a : Type) . List (List a) -> List a
  = /\(a : Type) . foldMap @(List a) @(List a) (id @(List a)) (additiveToMonoid @(List a) (listMon @a))

fun additiveIntegerMon : Monoid Integer
  = Mon @Integer (\(x : Integer) (y : Integer) . x + y) 0

fun length : all (a : Type) . List a -> Integer
  = /\(a : Type) . foldMap @a @Integer (\(x : a) . 1) additiveIntegerMon

fun main : Integer
  = length @Integer (concat @Integer (Nil @(List Integer)))

|]

destructors :: PrtUnorderedDefs Ex
destructors =
  [prog|
data Maybe (a : Type)
  = Just : a -> Maybe a
  | Nothing : Maybe a

fun val : Maybe (Integer -> Integer)
  = Just @(Integer -> Integer) (\(x : Integer) . x + 1)

fun main : Integer
  = match_Maybe @(Integer -> Integer) val @Integer (\(f : Integer -> Integer) . f 42) 0
|]

-- Here's a tricky situation! We need the defunctionalizer to pick up that
-- the definition of 'Predicate' has to be updated, even though it doesn't
-- contain a function type directly
indirect :: PrtUnorderedDefs Ex
indirect =
  [prog|
data Predicate (a : Type)
  = Prob : Maybe (Integer -> a) -> Predicate a

data Maybe (a : Type)
  = Just : a -> Maybe a
  | Nothing : Maybe a

fun run : all (a : Type) . Predicate a -> Integer -> Maybe a
  = /\(a : Type) . \(p : Predicate a) (x : Integer)
    . match_Predicate @a p @(Maybe a)
        (\(mf : Maybe (Integer -> a))
         . match_Maybe @(Integer -> a) mf @(Maybe a)
             (\f : Integer -> a . Just @a (f x))
             (Nothing @a))

fun val : Predicate Bool
  = Prob @Bool (Just @(Integer -> Bool) (\(x : Integer) . x < 1))

fun main : Bool
  = match_Maybe @Bool (run @Bool val 42) @Bool (\x : Bool . x) False
|]

-- While we're at it, let's throw in a mixed definition that has both direct
-- and indirect needs for defunctionalization in the same type!
mixed :: PrtUnorderedDefs Ex
mixed =
  [prog|
data Mixed (a : Type)
  = Mix : a -> (a -> a) -> Mixed a

fun run : all (a : Type) . Mixed a -> a
  = /\(a : Type) . \(m : Mixed a) . match_Mixed @a m @a
      (\(x : a) (f : a -> a) . f x)

data Maybe (a : Type)
  = Just : a -> Maybe a
  | Nothing : Maybe a

fun or : Bool -> Bool -> Bool
  = \(x : Bool) (y : Bool) . if @Bool x then True else y

-- The worst nightmare of the defunctionalizer! :)
fun nasty : Mixed (Maybe (Bool -> Bool))
  = Mix @(Maybe (Bool -> Bool))
        (Just @(Bool -> Bool) (or True))
        (\(x : Maybe (Bool -> Bool)) . Nothing @(Bool -> Bool))

fun main : Bool
  = match_Maybe @(Bool -> Bool) (run @(Maybe (Bool -> Bool)) nasty) @Bool
      (\(f : Bool -> Bool) . f True)
      False
|]
