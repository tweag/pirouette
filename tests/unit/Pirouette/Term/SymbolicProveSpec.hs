{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module Pirouette.Term.SymbolicProveSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Symbolic.Eval
import Pirouette.Term.Symbolic.Prover
import Pirouette.Transformations ( elimEvenOddMutRec )
import Test.Tasty
import Test.Tasty.HUnit

import Pirouette.Term.SymbolicEvalUtils

exec :: (Program Ex, Type Ex, Term Ex) -> (Term Ex, Term Ex)
     -> IO (Either String [Path Ex (EvaluationWitness Ex)])
exec (program, tyRes, fn) (assume, toProve) = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ 
    prove (Problem tyRes fn assume toProve)

add1 :: (Program Ex, Type Ex, Term Ex)
add1 = (
  [prog|
fun add1 : Integer -> Integer
  = \(x : Integer) . x + 1

fun greaterThan0 : Integer -> Bool
  = \(x : Integer) . 0 < x

fun greaterThan1 : Integer -> Bool
  = \(x : Integer) . 1 < x

fun main : Integer = 42
  |],
  [ty|Integer|],
  [term| \(x : Integer) . add1 x |])

add1TripleWrong :: (Term Ex, Term Ex)
add1TripleWrong = (
  [term| \(result : Integer) (x : Integer) . greaterThan0 result |],
  [term| \(result : Integer) (x : Integer) . greaterThan0 x |])

add1TripleOk :: (Term Ex, Term Ex)
add1TripleOk = (
  [term| \(result : Integer) (x : Integer) . greaterThan1 result |],
  [term| \(result : Integer) (x : Integer) . greaterThan0 x |])

switchSides :: (Term Ex, Term Ex) -> (Term Ex, Term Ex)
switchSides (assume, prove) = (prove, assume)

tests :: [TestTree]
tests = [
  testGroup "incorrectness triples" 
    [ testCase "[input > 0] add 1 [result > 0] fails" $
        exec add1 add1TripleWrong `pathSatisfies` singleCounter,
      testCase "[input > 0] add 1 [result > 1] ok" $
        exec add1 add1TripleOk `pathSatisfies` singleVerified 
    ],
  testGroup "Hoare triples" 
    [ testCase "{input > 0} add 1 {result > 0} ok" $
        exec add1 (switchSides add1TripleWrong) `pathSatisfies` singleVerified,
      testCase "{input > 0} add 1 {result > 1} ok" $
        exec add1 (switchSides add1TripleOk) `pathSatisfies` singleVerified
    ]
  ]