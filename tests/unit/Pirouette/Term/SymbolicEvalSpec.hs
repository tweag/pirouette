{-# LANGUAGE DerivingStrategies #-}
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

symbolicExec' :: (Program Ex, Term Ex) -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExec' = uncurry symbolicExec

symbolicExec :: Program Ex -> Term Ex -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExec program term = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ do
    pathsFor (Fuel 10) "main" term

incorrectnessExec' :: (Program Ex, Term Ex) -> (Constraint Ex, TermMeta Ex SymVar -> Constraint Ex)
                   -> IO (Either String [Path Ex (EvaluationWitness Ex)])
incorrectnessExec' (p, t) (i, o) = incorrectnessExec p t (InCond i) (OutCond o)

incorrectnessExec :: Program Ex -> Term Ex -> InCond Ex -> OutCond Ex
                  -> IO (Either String [Path Ex (EvaluationWitness Ex)])
incorrectnessExec program term inC outC = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ do
    pathsIncorrectness UserDeclaredConstraints {
      udcInputs = [], 
      udcOutputCond = outC, 
      udcInputCond = inC, 
      udcAdditionalDefs = pure [], 
      udcAxioms = [] } 
      term

(*=*) :: (Eq a, Show a) => IO (Either String a) -> a -> Assertion
thing *=* expected = do
  given <- thing
  case given of
    Left e -> assertFailure $ "finished with errors: " <> e
    Right x -> x @=? expected

satisfies :: (Eq a, Show a) => IO (Either String a) -> (a -> Bool) -> Assertion
thing `satisfies` property = do
  given <- thing
  case given of
    Left e -> assertFailure $ "finished with errors: " <> e
    Right x -> assertBool ("property not satisfied: " <> show x) (property x)

add1 :: (Program Ex, Term Ex)
add1 = (
  [prog|
fun sumar : Integer -> Integer -> Integer
  = \(x : Integer) (y : Integer) . x + y

fun main : Integer = 42
  |],
  [term| \(z : Integer) . sumar z 1 |])

botConditions :: (Constraint Ex, TermMeta Ex SymVar -> Constraint Ex)
botConditions = (SMT.Bot, const mempty)

topConditions :: (Constraint Ex, TermMeta Ex SymVar -> Constraint Ex)
topConditions = (mempty, const mempty)

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False

tests :: [TestTree]
tests = [ 
  testCase "add 1" $
    symbolicExec' add1 `satisfies` isSingleton,
  testCase "add 1, bot" $
    incorrectnessExec' add1 botConditions `satisfies` isSingleton,
  testCase "add 1, top" $
    incorrectnessExec' add1 topConditions `satisfies` null
  ]