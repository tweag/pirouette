{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Transformations.EtaExpandSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Transformations.EtaExpand
import Test.Tasty
import Test.Tasty.HUnit

withUnorderedDecls ::
  Program Ex ->
  (forall m. PirouetteReadDefs Ex m => m Assertion) ->
  Assertion
withUnorderedDecls (decls, main) m =
  case mockPrt (runReaderT m (PrtUnorderedDefs decls main)) of
    Left err -> assertFailure err
    Right t -> t

sampleProgram :: Program Ex
sampleProgram =
  [prog|
data Maybe (a : Type)
  = Nothing : Maybe a
  | Just : a -> Maybe a

fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun const : all (a : Type) (b : Type) . a -> b -> a
    = /\ (a : Type) (b : Type) . \ (x : a) (y : b) . x

fun main : Integer = 42
|]

isEtaEq :: Term Ex -> Term Ex -> Assertion
isEtaEq t u = withUnorderedDecls sampleProgram $ do
  res <- etaExpandTerm t
  return $ unless (res == u) (assertFailure $ msg res)
  where
    msg res =
      concat
        [ "expected: ",
          renderSingleLineStr (pretty u),
          "\n but got: ",
          renderSingleLineStr (pretty res)
        ]

tests :: [TestTree]
tests =
  [ testCase "add ~ \\x y -> add x y" $
      [term| add |] `isEtaEq` [term| \(x : Integer) (y : Integer) . add x y |],
    testCase "f (add 42) ~ f (\\x -> add 42 x)" $
      [term| f (add 42) |] `isEtaEq` [term| f (\ x : Integer . add 42 x) |],
    testCase "const ~  /\\(a : Type) (b : Type) . \\(x : a) (y : b) . const @a @b x y" $
      [term| const |] `isEtaEq` [term| /\(a : Type) (b : Type) . \(x : a) (y : b) . const @a @b x y |]
  ]
