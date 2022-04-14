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

input0Output0 :: (Term Ex, Term Ex)
input0Output0 = (
  [term| \(result : Integer) (x : Integer) . greaterThan0 result |],
  [term| \(result : Integer) (x : Integer) . greaterThan0 x |])

input0Output1 :: (Term Ex, Term Ex)
input0Output1 = (
  [term| \(result : Integer) (x : Integer) . greaterThan1 result |],
  [term| \(result : Integer) (x : Integer) . greaterThan0 x |])

maybes :: Program Ex
maybes = [prog|
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

switchSides :: (Term Ex, Term Ex) -> (Term Ex, Term Ex)
switchSides (assume, prove) = (prove, assume)

tests :: [TestTree]
tests = [
  testGroup "incorrectness triples" 
    [ testCase "[input > 0] add 1 [result > 0] counter" $
        exec add1 input0Output0 `pathSatisfies` (isSingleton .&. all isCounter),
      testCase "[input > 0] add 1 [result > 1] verified" $
        exec add1 input0Output1 `pathSatisfies` (isSingleton .&. all isVerified),
      testCase "[isNothing x] isJust x [not result] verified" $
        exec (maybes, [ty|Bool|], [term|\(x:MaybeInt) . isJust x|]) 
             ([term|\(r:Bool) (x:MaybeInt) . not r|], [term|\(r:Bool) (x:MaybeInt) . isNothing x|])
          `pathSatisfies` (all isNoCounter .&. any isVerified),
      testCase "[isJust x] isJust x [not result] counter" $
        exec (maybes, [ty|Bool|], [term|\(x:MaybeInt) . isJust x|]) 
             ([term|\(r:Bool) (x:MaybeInt) . not r|], [term|\(r:Bool) (x:MaybeInt) . isJust x|])
          `pathSatisfies` any isCounter
    ],
  testGroup "Hoare triples" 
    [ testCase "{input > 0} add 1 {result > 0} verified" $
        exec add1 (switchSides input0Output0) `pathSatisfies` (isSingleton .&. all isVerified),
      testCase "{input > 0} add 1 {result > 1} verified" $
        exec add1 (switchSides input0Output1) `pathSatisfies` (isSingleton .&. all isVerified)
    ]
  ]