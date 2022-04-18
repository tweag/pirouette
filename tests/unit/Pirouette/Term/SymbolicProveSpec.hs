{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Term.SymbolicProveSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import Pirouette.Term.Symbolic.Eval
import Pirouette.Term.Symbolic.Prover
import Pirouette.Term.SymbolicEvalUtils
import Pirouette.Term.Syntax.Base
import Pirouette.Transformations (elimEvenOddMutRec)
import Test.Tasty
import Test.Tasty.HUnit

exec ::
  (Program Ex, Type Ex, Term Ex) ->
  (Term Ex, Term Ex) ->
  IO (Either String [Path Ex (EvaluationWitness Ex)])
exec (program, tyRes, fn) (assume, toProve) = fmap fst $
  mockPrtT $ do
    let decls = uncurry PrtUnorderedDefs program
    orderedDecls <- elimEvenOddMutRec decls
    flip runReaderT orderedDecls $
      prove (Problem tyRes fn assume toProve)

add1 :: (Program Ex, Type Ex, Term Ex)
add1 =
  ( [prog|
fun add1 : Integer -> Integer
  = \(x : Integer) . x + 1

fun greaterThan0 : Integer -> Bool
  = \(x : Integer) . 0 < x

fun greaterThan1 : Integer -> Bool
  = \(x : Integer) . 1 < x

fun main : Integer = 42
  |],
    [ty|Integer|],
    [term| \(x : Integer) . add1 x |]
  )

input0Output0 :: (Term Ex, Term Ex)
input0Output0 =
  ( [term| \(result : Integer) (x : Integer) . greaterThan0 result |],
    [term| \(result : Integer) (x : Integer) . greaterThan0 x |]
  )

input0Output1 :: (Term Ex, Term Ex)
input0Output1 =
  ( [term| \(result : Integer) (x : Integer) . greaterThan1 result |],
    [term| \(result : Integer) (x : Integer) . greaterThan0 x |]
  )

maybes :: Program Ex
maybes =
  [prog|
data MaybeInt
  = JustInt : Integer -> Maybe Int
  | NothingInt : Maybe Int

fun isNothing : MaybeInt -> Bool
  = \(m : MaybeInt) . match_MaybeInt m @Bool (\(n : Integer) . False) True

fun isJust : MaybeInt -> Bool
  = \(m : MaybeInt) . match_MaybeInt m @Bool (\(n : Integer) . True) False

fun not : Bool -> Bool
  = \(b : Bool) . if @Bool b then False else True

fun main : Integer = 42
|]

-- This is a small example taken from O'Hearn's paper; besides being interesting for
-- testing conditionals, it is also interesting in and of itself. This is the example:
--
-- > [z == 11]
-- > if (even x) {
-- >   if (odd y) {
-- >     z == 42
-- >   }
-- > }
-- > [z == 42]
--
-- Do you think the IL triple above is satisfiable? Surprisingly, it's not. In the imperative setting,
-- the statement @[P] f [Q]@ means that forall state s1 satisfying @Q@, there exists s0 such that s1 is reachable
-- from s0 by f and s0 satisfies @P@. With that in mind, the state @[(z, 42), (x, 3), (y, 2)]@ satisfies @Q@
-- and, albeit reachable, it is not reachable from a state satisfying the precondition @z == 11@.
-- Therefore the IL triple is falsifiable and we'd expect such a counterexample from our tool.
-- A IL triple really /means/:
--
-- > [P] f [Q] <=> { s' | s' \in post f && Q s' } \subseteq { f s | P s }
--
-- Which makes it obvious that, @[(z, 42), (x, 3), (y, 2)]@ is both a post state and satisfies Q,
-- but its not an element of { f s | P s } because all elements of that set satisfy z == 11.
--
-- If we enrich our postcondition to read:
--
-- > [z == 42 && even x && odd y]
--
-- Now we have a valid IL triple, and this provides an interesting test case for pirouette.
-- Firstly, though, we have to translate the semantics of triples. In a pure setting we have
-- no notion of reachability, only termination. Hence,
--
-- [P] f [Q] <=> { o | \Ex i . o = f i && Q o } \subseteq { f i | P i }
--
-- Which translates to:
--
-- >    forall x . x \in { o | \Ex i . o = f i && Q o } `implies` x \in { f i | P i }
-- > == forall x . (\Ex i1 . x = f i1 && Q x) `implies` (\Ex i2 . P i2 && x = f i2)
--
-- (TODO: Exercise for the writer: double check these statements!)
--
-- To translate the code block given by O'Hearn on their paper to Haskell, we could get
-- something like:
--
-- > ohearn :: (Integer, Integer) -> (Integer, Integer)
-- > ohearn x y
-- >   | even x = (x, 42)
-- >   | otherwise = (x, y)
--
-- Now, if we ask the question of whether or not the following triple is valid:
--
-- > [\(x, y) -> y == 11] ohearn [\(rx, ry) (x, y) -> ry == 42]
--
-- Or, in other words:
--
-- > forall rx ry . (\Ex x y . (rx, ry) == f (x, y) && ry == 42) `implies` (\Ex x y . (rx, ry) == f (x, y) && y == 11)
--
-- It's still not valid! A similar model gives us a counterexample: f (3, 42) == (3, 42) && y /= 11
-- In fact, any choice of an odd value for the first component of the input pair will yield a counterexample.
-- Again, strengthtening the postcondition gives us a valid triple:
--
-- > [\(x, y) -> y == 11] ohearn [\(rx, ry) (x, y) -> even x && ry == 42]
--

conditionals1 :: (Program Ex, Type Ex, Term Ex)
conditionals1 =
  ( [prog|
data Delta = D : Integer -> Integer -> Delta

fun fst : Delta -> Integer
  = \(x : Delta) . match_Delta x @Integer (\(a : Integer) (b : Integer) . a)

fun snd : Delta -> Integer
  = \(x : Delta) . match_Delta x @Integer (\(a : Integer) (b : Integer) . b)

fun even : Integer -> Bool
  = \(x : Integer) . if @Bool x == 0 then True else odd (x - 1)

fun odd : Integer -> Bool
  = \(x : Integer) . if @Bool x == 0 then False else even (x - 1)

fun and : Bool -> Bool -> Bool
  = \(x : Bool) (y : Bool) . if @Bool x then y else False

fun ohearn : Delta -> Delta
  = \(xy : Delta)
  . if @Delta even (fst xy)
    then D (fst xy) 42
    else xy

fun main : Integer = 42
  |],
    [ty|Delta|],
    [term| \(x : Delta) . ohearn x |]
  )

condWrongTriple :: (Term Ex, Term Ex)
condWrongTriple =
  ( [term| \(result : Delta) (x : Delta) . snd x == 11 |],
    [term| \(result : Delta) (x : Delta) . snd result == 42 |]
  )

condCorrectTriple :: (Term Ex, Term Ex)
condCorrectTriple =
  ( [term| \(result : Delta) (x : Delta) . snd x == 11 |],
    [term| \(result : Delta) (x : Delta) . (and (snd result == 42) (even (fst result))) |]
  )

ohearnTest :: TestTree
ohearnTest =
  testGroup
    "OHearn"
    [ testCase "[y == 11] ohearn [snd result == 42] counter" $
        let isValidCounter = \case
              SimpleSMT.Other (SimpleSMT.List [SimpleSMT.Atom "pir_D", SimpleSMT.Atom fstX, _]) -> odd (read fstX)
              _ -> False
         in exec conditionals1 condWrongTriple `pathSatisfies` all (isCounterWith $ maybe False isValidCounter . lookup (SimpleSMT.Atom "pir_x")),
      testCase "[y == 11] ohearn [snd result == 42 && even (fst result)] verified" $
        exec conditionals1 condCorrectTriple `pathSatisfies` all isVerified
    ]

-- We didn't have much success with builtins integers; let me try the same with peano naturals:

conditionals1Peano :: (Program Ex, Type Ex, Term Ex)
conditionals1Peano =
  ( [prog|
data Nat = Z : Nat | S : Nat -> Nat

fun eq : Nat -> Nat -> Bool
  = \(x : Nat) (y : Nat)
  . match_Nat x @Bool
      (match_Nat y @Bool True (\(yy : Nat) . False))
      (\(xx : Nat) . match_Nat y @Bool False (\(yy : Nat) . eq xx yy))

fun even : Nat -> Bool
  = \(x : Nat) . match_Nat x @Bool True odd

fun odd : Nat -> Bool
  = \(x : Nat) . match_Nat x @Bool False even

data Delta = D : Nat -> Nat -> Delta

fun fst : Delta -> Nat
  = \(x : Delta) . match_Delta x @Nat (\(a : Nat) (b : Nat) . a)

fun snd : Delta -> Nat
  = \(x : Delta) . match_Delta x @Nat (\(a : Nat) (b : Nat) . b)

fun and : Bool -> Bool -> Bool
  = \(x : Bool) (y : Bool) . if @Bool x then y else False

fun ohearn : Delta -> Delta
  = \(xy : Delta)
  . if @Delta even (fst xy)
    then D (fst xy) (S (S Z))
    else xy

fun main : Integer = 42
  |],
    [ty|Delta|],
    [term| \(x : Delta) . ohearn x |]
  )

condWrongTriplePeano :: (Term Ex, Term Ex)
condWrongTriplePeano =
  ( [term| \(result : Delta) (x : Delta) . eq (snd x) (S Z)  |],
    [term| \(result : Delta) (x : Delta) . False -- eq (snd result) (S (S Z)) |]
  )

condCorrectTriplePeano :: (Term Ex, Term Ex)
condCorrectTriplePeano =
  ( [term| \(result : Delta) (x : Delta) . eq (snd x) (S Z) |],
    [term| \(result : Delta) (x : Delta) . (and (eq (snd result) (S (S Z))) (even (fst result))) |]
  )

-- XXX: The following tests are hitting the bug on Pirouette.SMT.Constraints, line 196

ohearnTestPeano :: TestTree
ohearnTestPeano =
  testGroup
    "OHearn Peano"
    [ testCase "[y == 1] ohearn-peano [snd result == 2] counter" $
        let isValidCounter = \case
              SimpleSMT.Other (SimpleSMT.List [SimpleSMT.Atom "pir_D", SimpleSMT.Atom fstX, _]) -> odd (read fstX)
              _ -> False
         in exec conditionals1Peano condWrongTriplePeano `pathSatisfies` all isVerified -- (isCounterWith $ maybe False isValidCounter . lookup (SimpleSMT.Atom "pir_x")),
      -- testCase "[y == 1] ohearn-peano [snd result == 2 && even (fst result)] verified" $
      --   exec conditionals1Peano condCorrectTriplePeano `pathSatisfies` all isVerified
    ]

switchSides :: (Term Ex, Term Ex) -> (Term Ex, Term Ex)
switchSides (assume, prove) = (prove, assume)

tests :: [TestTree]
tests =
  [ testGroup
      "incorrectness triples"
      [ testCase "[input > 0] add 1 [result > 0] counter" $
          exec add1 input0Output0 `pathSatisfies` (isSingleton .&. all isCounter),
        testCase "[input > 0] add 1 [result > 1] verified" $
          exec add1 input0Output1 `pathSatisfies` (isSingleton .&. all isVerified),
        testCase "[isNothing x] isJust x [not result] verified" $
          exec
            (maybes, [ty|Bool|], [term|\(x:MaybeInt) . isJust x|])
            ([term|\(r:Bool) (x:MaybeInt) . not r|], [term|\(r:Bool) (x:MaybeInt) . isNothing x|])
            `pathSatisfies` (all isNoCounter .&. any isVerified),
        testCase "[isJust x] isJust x [not result] counter" $
          exec
            (maybes, [ty|Bool|], [term|\(x:MaybeInt) . isJust x|])
            ([term|\(r:Bool) (x:MaybeInt) . not r|], [term|\(r:Bool) (x:MaybeInt) . isJust x|])
            `pathSatisfies` any isCounter
      ],
    testGroup
      "Hoare triples"
      [ testCase "{input > 0} add 1 {result > 0} verified" $
          exec add1 (switchSides input0Output0) `pathSatisfies` (isSingleton .&. all isVerified),
        testCase "{input > 0} add 1 {result > 1} verified" $
          exec add1 (switchSides input0Output1) `pathSatisfies` (isSingleton .&. all isVerified)
      ],
    ohearnTest,
    ohearnTestPeano
  ]
