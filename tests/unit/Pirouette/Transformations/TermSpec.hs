{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Transformations.TermSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax.Base
import Pirouette.Transformations.Term
import Test.Tasty
import Test.Tasty.HUnit

withUnorderedDecls ::
  PrtUnorderedDefs Ex ->
  (forall m. PirouetteReadDefs Ex m => m Assertion) ->
  Assertion
withUnorderedDecls prog m =
  case runReaderT m prog of
    Left err -> assertFailure err
    Right t -> t

sampleProgram :: PrtUnorderedDefs Ex
sampleProgram =
  [prog|
data Maybe (a : Type)
  = Nothing : Maybe a
  | Just : a -> Maybe a

add : Integer -> Integer -> Integer
add x y = x + y

f1 : Maybe Integer -> Integer
f1 x = add (match_Maybe @Integer x @Integer 42 (\n : Integer . n)) 1

destrNF_f1 : Maybe Integer -> Integer
destrNF_f1 x = match_Maybe @Integer x @Integer (add 42 1) (\n : Integer . add n 1)
|]

tests :: [TestTree]
tests =
  [ testCase "destrNF" $
      withUnorderedDecls sampleProgram $ do
        destrNF_f1 <- prtTermDefOf "f1" >>= destrNF
        expected <- prtTermDefOf "destrNF_f1"
        return $ destrNF_f1 @?= expected
  ]
