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

symbolicExec :: Program Ex -> Term Ex -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExec program term = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ do
    pathsFor (\st -> sestConsumedFuel st > 10) "main" term

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
    incorrectnessExec' oneFake botConditions `pathSatisfies` (isSingleton .&. all isCounter)
  -- testCase "who knows should have two branches" $
  --   incorrectnessExec' whoKnows botConditions `pathSatisfies` (\x -> length x == 2)
  ]