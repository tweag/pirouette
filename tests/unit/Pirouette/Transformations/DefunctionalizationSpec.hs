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
add : Integer -> Integer -> Integer
add x y = x + y

apply : (Integer -> Integer) -> Integer -> Integer
apply f x = f x

two : Integer
two = apply (add 1) 1
|],
    [prog|
nonrec _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
_Apply!!TyInteger_TyInteger = \(cls : Closure!!TyInteger_TyInteger) .
      match_Closure!!TyInteger_TyInteger cls @(Integer -> Integer) (\(η : Integer) . add 1 η)

data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Closure!!TyInteger_TyInteger

add : Integer -> Integer -> Integer
add x y = x + y

apply : Closure!!TyInteger_TyInteger -> Integer -> Integer
apply f x = _Apply!!TyInteger_TyInteger f x

two : Integer
two = apply Closure!!TyInteger_TyInteger_ctor_0 1
|]
  )

addConst, addConstDefunc :: PrtUnorderedDefs Ex
(addConst, addConstDefunc) =
  ( [prog|
add : Integer -> Integer -> Integer
add x y = x + y

const : Integer -> Integer -> Integer
const x y = x

apply : (Integer -> Integer) -> Integer -> Integer
apply f x = f x

two : Integer
two = apply (add 1) 1

three : Integer
three = apply (const 3) 10

four : Integer
four = apply (apply (add 2)) 2
|],
    [prog|
data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_1 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_2 : Closure!!TyInteger_TyInteger
  | Closure!!TyInteger_TyInteger_ctor_3 : Closure!!TyInteger_TyInteger

nonrec _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
_Apply!!TyInteger_TyInteger cls =
      match_Closure!!TyInteger_TyInteger cls @(Integer -> Integer)
        (\(η : Integer) . add 2 η)
        (\(η : Integer) . apply Closure!!TyInteger_TyInteger_ctor_0 η)
        (\(η : Integer) . const 3 η)
        (\(η : Integer) . add 1 η)

add : Integer -> Integer -> Integer
add x y = x + y

apply : Closure!!TyInteger_TyInteger -> Integer -> Integer
apply f x = _Apply!!TyInteger_TyInteger f x

const : Integer -> Integer -> Integer
const x y = x

four : Integer
four = apply Closure!!TyInteger_TyInteger_ctor_1 2

three : Integer
three = apply Closure!!TyInteger_TyInteger_ctor_2 10

two : Integer
two = apply Closure!!TyInteger_TyInteger_ctor_3 1
|]
  )

dataType, dataTypeDefunc :: PrtUnorderedDefs Ex
(dataType, dataTypeDefunc) =
  ( [prog|
data IntHomo
  = IntHomoC : (Integer -> Integer) -> IntHomo

applyIntHomoToOne : IntHomo -> Integer
applyIntHomoToOne h = match_IntHomo h @Integer (\(f : Integer -> Integer) . f 1)

main : Integer -> Integer
main k = applyIntHomoToOne (IntHomoC (\(x : Integer) . x + k))
|],
    [prog|
data Closure!!TyInteger_TyInteger
  = Closure!!TyInteger_TyInteger_ctor_0 : Integer -> Closure!!TyInteger_TyInteger

data IntHomo
  = IntHomoC : Closure!!TyInteger_TyInteger -> IntHomo

nonrec _Apply!!TyInteger_TyInteger : Closure!!TyInteger_TyInteger -> Integer -> Integer
_Apply!!TyInteger_TyInteger cls =
      match_Closure!!TyInteger_TyInteger cls @(Integer -> Integer) (\(k : Integer) (η : Integer) . η + k)

applyIntHomoToOne : IntHomo -> Integer
applyIntHomoToOne h = match_IntHomo h @Integer (\(f : Closure!!TyInteger_TyInteger) . _Apply!!TyInteger_TyInteger f 1)

main : Integer -> Integer
main k = applyIntHomoToOne (IntHomoC (Closure!!TyInteger_TyInteger_ctor_0 k))
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
            Left err -> print (pretty decls) >> assertFailure (show $ pretty err)
            Right _ -> return ()

nested :: PrtUnorderedDefs Ex
nested =
  [prog|
data Monoid (a : *)
  = Mon : (a -> a -> a) -> a -> Monoid a

data AdditiveMonoid (a : *)
  = AdditiveMon : (a -> a -> a) -> a -> AdditiveMonoid a

additiveToMonoid : forall a . AdditiveMonoid a -> Monoid a
additiveToMonoid @a x = 
    Mon @a (match_AdditiveMonoid @a x @(a -> a -> a) (\(f : a -> a -> a) (z : a) . f))
           (match_AdditiveMonoid @a x @a (\(f : a -> a -> a) (z : a) . z))

data List (a : *)
  = Nil : List a
  | Cons : a -> List a -> List a

listMon : forall a . AdditiveMonoid (List a)
listMon @a = AdditiveMon @(List a) (\(k : List a) (l : List a)
    . foldr @a @(List a) (Cons @a) l k) (Nil @a)

foldr : forall (a : *) (b : *) . (a -> b -> b) -> b -> List a -> b
foldr @a @b f m xs =
   match_List @a xs @b
     m
     (\(h : a) (tl : List a) . f h (foldr @a @b f m tl))

foldMap : forall (a : *) (b : *) . (a -> b) -> Monoid b -> List a -> b
foldMap @a @b f m xs =
  match_Monoid @b m @b
    (\ (mplus : b -> b -> b) (mzero : b)
     . foldr @a @b (\(x : a) (rest : b) . mplus (f x) rest) mzero xs
    )

id : forall a . a -> a
id @a x = x

concat : forall a . List (List a) -> List a
concat @a = foldMap @(List a) @(List a) (id @(List a)) (additiveToMonoid @(List a) (listMon @a))

additiveIntegerMon : Monoid Integer
additiveIntegerMon = Mon @Integer (\(x : Integer) (y : Integer) . x + y) 0

length : forall a . List a -> Integer
length @a = foldMap @a @Integer (\(x : a) . 1) additiveIntegerMon

main : Integer
main = length @Integer (concat @Integer (Nil @(List Integer)))

|]

destructors :: PrtUnorderedDefs Ex
destructors =
  [prog|
data Maybe (a : *)
  = Just : a -> Maybe a
  | Nothing : Maybe a

val : Maybe (Integer -> Integer)
val = Just @(Integer -> Integer) (\(x : Integer) . x + 1)

main : Integer
main = match_Maybe @(Integer -> Integer) val @Integer (\(f : Integer -> Integer) . f 42) 0
|]

-- Here's a tricky situation! We need the defunctionalizer to pick up that
-- the definition of 'Predicate' has to be updated, even though it doesn't
-- contain a function type directly
indirect :: PrtUnorderedDefs Ex
indirect =
  [prog|
data Predicate (a : *)
  = Prob : Maybe (Integer -> a) -> Predicate a

data Maybe (a : *)
  = Just : a -> Maybe a
  | Nothing : Maybe a

run : forall a . Predicate a -> Integer -> Maybe a
run @a p x =
    match_Predicate @a p @(Maybe a)
      (\(mf : Maybe (Integer -> a))
       . match_Maybe @(Integer -> a) mf @(Maybe a)
           (\f : Integer -> a . Just @a (f x))
           (Nothing @a))

val : Predicate Bool
val = Prob @Bool (Just @(Integer -> Bool) (\(x : Integer) . x < 1))

main : Bool
main = match_Maybe @Bool (run @Bool val 42) @Bool (\x : Bool . x) False
|]

-- While we're at it, let's throw in a mixed definition that has both direct
-- and indirect needs for defunctionalization in the same type!
mixed :: PrtUnorderedDefs Ex
mixed =
  [prog|
data Mixed (a : *)
  = Mix : a -> (a -> a) -> Mixed a

run : forall a . Mixed a -> a
run @a m = match_Mixed @a m @a (\(x : a) (f : a -> a) . f x)

data Maybe (a : *)
  = Just : a -> Maybe a
  | Nothing : Maybe a

or : Bool -> Bool -> Bool
or x y = if @Bool x then True else y

-- The worst nightmare of the defunctionalizer! :)
nasty : Mixed (Maybe (Bool -> Bool))
nasty = Mix @(Maybe (Bool -> Bool))
        (Just @(Bool -> Bool) (or True))
        (\(x : Maybe (Bool -> Bool)) . Nothing @(Bool -> Bool))

main : Bool
main = match_Maybe @(Bool -> Bool) (run @(Maybe (Bool -> Bool)) nasty) @Bool
      (\(f : Bool -> Bool) . f True)
      False
|]
