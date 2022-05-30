{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module Pirouette.Term.SymbolicEvalSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Symbolic.Eval
import Pirouette.Transformations ( elimEvenOddMutRec )
import Test.Tasty
import Test.Tasty.HUnit
import qualified Pirouette.SMT as SMT
import qualified Pirouette.SMT.SimpleSMT as SMT

import Pirouette.Term.SymbolicEvalUtils

symbolicExec' :: (Program Ex, Term Ex) -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExec' = uncurry symbolicExec

symbolicExecCtors' :: Int -> (Program Ex, Term Ex) -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExecCtors' = uncurry . symbolicExecCtors

symbolicExec :: Program Ex -> Term Ex -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExec program term = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ do
    pathsFor (\st -> sestConsumedFuel st > 10) "main" term

symbolicExecCtors :: Int -> Program Ex -> Term Ex -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExecCtors depth program term = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ do
    pathsFor (\st -> sestConstructors st > depth) "main" term

incorrectnessExec' :: (Program Ex, Term Ex) -> (Constraint Ex, TermMeta Ex SymVar -> Constraint Ex)
                   -> IO (Either String [Path Ex (EvaluationWitness Ex)])
incorrectnessExec' (p, t) (i, o) = incorrectnessExec p t (InCond i) (OutCond o)

incorrectnessExec :: Program Ex -> Term Ex -> InCond Ex -> OutCond Ex
                  -> IO (Either String [Path Ex (EvaluationWitness Ex)])
incorrectnessExec program term inC outC = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ do
    pathsIncorrectness (const False) UserDeclaredConstraints {
      udcInputs = [],
      udcOutputCond = outC,
      udcInputCond = inC,
      udcAdditionalDefs = pure [],
      udcAxioms = [] }
      term

add1 :: (Program Ex, Term Ex)
add1 = (
  [prog|
fun sumar : Integer -> Integer -> Integer
  = \(x : Integer) (y : Integer) . x + y

fun main : Integer = 42
  |],
  [term| \(z : Integer) . sumar z 1 |])

oneFake :: (Program Ex, Term Ex)
oneFake = (
  [prog|
fun oneFake : Integer -> Integer -> Integer
  = \(x : Integer) (y : Integer) . if @Integer 1 < 0 then x else y

fun main : Integer = 42
  |],
  [term| \(x : Integer) (y : Integer) . oneFake x y |])

whoKnows :: (Program Ex, Term Ex)
whoKnows = (
  [prog|
fun whoKnows : Integer -> Integer -> Integer -> Integer
  = \(n : Integer) (x : Integer) (y : Integer) . if @Integer n < 0 then x else y

fun main : Integer = 42
  |],
  [term| \(n : Integer) (x : Integer) (y : Integer) . whoKnows n x y |])

stateSpaceExploration :: (Program Ex, Term Ex)
stateSpaceExploration = (
  [prog|
data ListOfInteger
  = Nil : ListOfInteger
  | Cons : Integer -> ListOfInteger -> ListOfInteger

data PairOfLists
  = MkPair : ListOfInteger -> ListOfInteger -> PairOfLists

-- match_ListOfInteger : ListOfInteger -> all (a : Type) -> a -> (Integer -> ListOfInteger -> a) -> a
fun sumList : ListOfInteger -> Integer
  = \(xs : ListOfInteger) .
    match_ListOfInteger xs @Integer
      0
      (\(y : Integer) (ys : ListOfInteger) . y + sumList ys)

fun main : Integer = 42
  |],
  [term| \(xs : PairOfLists) . match_PairOfLists xs @Integer
           (\(fst : ListOfIntegers) (snd : ListOfIntegers) . sumList fst + sumList snd)
       |])


singleConstructor :: (Program Ex, Term Ex)
singleConstructor = (
  [prog|
data A
  = Val : Integer -> A

fun getVal : A -> Integer
  = \(v : A) .
    match_A v @Integer
      (\(y : Integer) . y)

fun main : Integer = 42
  |],
  [term| \(v : A) . getVal v
       |])

-- TODO: Add a test that checks that all paths that are produced contain the expected terms in the expected order.
-- For instance, for the stopping condition of (\stats -> numConstructors > 5), we should see
-- the following paths:
--
-- > ([], []) (_ : [], []) ([], _ : []) (_ : [], _ : []) (_ : _ : [], []) ([], _ : _ : [])
--


botConditions :: (Constraint Ex, TermMeta Ex SymVar -> Constraint Ex)
botConditions = (SMT.Bot, const mempty)

topConditions :: (Constraint Ex, TermMeta Ex SymVar -> Constraint Ex)
topConditions = (mempty, const mempty)

tests :: [TestTree]
tests = [
  testCase "add 1" $
    symbolicExec' add1 `satisfies` isSingleton,
  testCase "add 1, bot" $
    incorrectnessExec' add1 botConditions `pathSatisfies` (isSingleton .&. all isCounter),
  testCase "add 1, top" $
    incorrectnessExec' add1 topConditions `pathSatisfies` (isSingleton .&. all isVerified),
  testCase "one fake branch" $
    incorrectnessExec' oneFake botConditions `pathSatisfies` (isSingleton .&. all isCounter),
  -- testCase "who knows should have two branches" $
  --   incorrectnessExec' whoKnows botConditions `pathSatisfies` (\x -> length x == 2)

  testCase "pairs of lists - depth 0" $
    symbolicExecCtors' 0 stateSpaceExploration `satisfies` isSingleton,

  -- Nil s1, (Cons s2 s3) s1
  testCase "pairs of lists - depth 1" $
    symbolicExecCtors' 1 stateSpaceExploration `satisfies` exactlyKElements 2,

  -- Nil Nil, Nil (Cons s2 s3), (Cons s2 Nil) s1, (Cons s2 (Cons s4 s5)) s2
  testCase "pairs of lists - depth 2" $
    symbolicExecCtors' 2 stateSpaceExploration `satisfies` exactlyKElements 4,

  -- Nil Nil, Nil (Cons s2 Nil), Nil (Cons s2 (Cons s4 s5)),
  -- (Cons s2 Nil) Nil, (Cons s2 (Cons s4 s5)) Nil, (Cons s2 Nil) (Cons s4 Nil),
  -- (Cons s2 Nil) (Cons s4 (Cons s6 s7)), (Cons s2 (Cons s6 s7)) (Cons s4 Nil),
  -- (Cons s2 (Cons s6 s7)) (Cons s4 (Cons s8 s9))
  testCase "pairs of lists - depth 3" $
    symbolicExecCtors' 3 stateSpaceExploration `satisfies` exactlyKElements 9,

  testCase "pairs of lists - depth 4" $
    symbolicExecCtors' 4 stateSpaceExploration `satisfies` exactlyKElements 11,

  testCase "pairs of lists - depth 5" $
    symbolicExecCtors' 5 stateSpaceExploration `satisfies` exactlyKElements 18,

  testCase "single constructor: parallel unfolding" $
    symbolicExecCtors' 1 singleConstructor `satisfies` isSingleton

  ]
