{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module Pirouette.Term.TransformationsSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Transformations
import Test.Tasty
import Test.Tasty.HUnit

withUnorderedDecls ::
  Program Ex ->
  (forall m. PirouetteReadDefs Ex m => m Assertion) ->
  Assertion
withUnorderedDecls (decls, main) m =
  case runReaderT m (PrtUnorderedDefs decls main) of
    Left err -> assertFailure err
    Right t  -> t

sampleProgram :: Program Ex
sampleProgram = [prog|
data Maybe (a : Type)
  = Nothing : Maybe a
  | Just : a -> Maybe a

fun add : Integer -> Integer -> Integer
    = \(x : Integer) (y : Integer) . x + y

fun f1 : Maybe Integer -> Integer
    = \x : Maybe Integer .
      add (match_Maybe @Integer x @Integer 42 (\n : Integer . n)) 1

fun destrNF_f1 : Maybe Integer -> Integer
    = \x : Maybe Integer .
      match_Maybe @Integer x @Integer (add 42 1) (\n : Integer . add n 1)

fun main : Integer = 42
|]

tests :: [TestTree]
tests = [
  testCase "destrNF" $ withUnorderedDecls sampleProgram $ do
      destrNF_f1 <- prtTermDefOf "f1" >>= destrNF
      expected <- prtTermDefOf "destrNF_f1"
      return $ destrNF_f1 @?= expected
  ]
