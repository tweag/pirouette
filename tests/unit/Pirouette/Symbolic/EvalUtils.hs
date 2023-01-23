{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Pirouette.Symbolic.EvalUtils where

import Data.List (intersperse)
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.Pretty
import Prettyprinter (vsep)
import Test.Tasty.HUnit

(*=*) :: (Eq a, Show a) => IO (Either String a) -> a -> Assertion
thing *=* expected = do
  given <- thing
  case given of
    Left e -> assertFailure $ "finished with errors: " <> e
    Right x -> x @=? expected

satisfies ::
  (Show a) =>
  IO a ->
  (a -> Bool) ->
  Assertion
thing `satisfies` property = do
  x <- thing
  assertBool ("property not satisfied: " <> show x) (property x)

pathSatisfies ::
  (Language lang, Pretty res, Show res) =>
  IO [Path lang res] ->
  ([Path lang res] -> Bool) ->
  Assertion
thing `pathSatisfies` property = do
  paths <- thing
  assertBool
    ( "`pathSatisfies`: the given property is not satisfied by the following paths:\n\n"
        <> show (vsep $ intersperse "" $ map pretty paths)
    )
    (property paths)

(.&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p .&. q = \x -> p x && q x

(.||.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p .||. q = \x -> p x || q x

isVerified,
  isDischarged,
  isCounter,
  isNoCounter,
  ranOutOfFuel ::
    Path lang (EvaluationWitness lang) -> Bool
isVerified Path {pathResult = Verified} = True
isVerified _ = False
isDischarged Path {pathResult = Discharged} = True
isDischarged _ = False
isCounter Path {pathResult = CounterExample _ _} = True
isCounter _ = False
ranOutOfFuel Path {pathStatus = OutOfFuel} = True
ranOutOfFuel _ = False

isCounterWith :: (Model -> Bool) -> Path lang (EvaluationWitness lang) -> Bool
isCounterWith f Path {pathResult = CounterExample _ m} = f m
isCounterWith f _ = False

isNoCounter = not . isCounter

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False
