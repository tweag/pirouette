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

symbolicExec' :: (Program Ex, Term Ex) -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExec' = uncurry symbolicExec

symbolicExec :: Program Ex -> Term Ex -> IO (Either String [Path Ex (TermMeta Ex SymVar)])
symbolicExec program term = fmap fst $ mockPrtT $ do
  let decls = uncurry PrtUnorderedDefs program
  orderedDecls <- elimEvenOddMutRec decls
  flip runReaderT orderedDecls $ do
    pathsFor (Fuel 10) "main" term

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
    Right x -> assertBool "property is not satisfied" $ property x

add1 :: (Program Ex, Term Ex)
add1 = (
  [prog|
fun sumar : Integer -> Integer -> Integer
  = \(x : Integer) (y : Integer) . x + y

fun main : Integer = 42
  |],
  [term| \(z : Integer) . sumar z 1 |])

tests :: [TestTree]
tests = [ 
  testCase "add 1" $
    symbolicExec' add1 `satisfies` (\r -> length r == 1)
  ]