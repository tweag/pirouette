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

-- ** Path Predicates

-- *** Combinators

-- | Logical conjunction of two predicates.
(.&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p .&. q = \x -> p x && q x

-- | Logical disjunction of two predicates.
(.||.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p .||. q = \x -> p x || q x

-- | Logical implication of two predicate.
(.=>.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p .=>. q = \x -> not (p x) || q x

-- *** Path Status Predicates

stillHasFuel :: Path lang (EvaluationWitness lang) -> Bool
stillHasFuel Path {pathStatus = OutOfFuel} = False
stillHasFuel _ = True

ranOutOfFuel :: Path lang (EvaluationWitness lang) -> Bool
ranOutOfFuel Path {pathStatus = OutOfFuel} = True
ranOutOfFuel _ = False

-- *** Path Result Predicates

isVerified :: Path lang (EvaluationWitness lang) -> Bool
isVerified Path {pathResult = Verified} = True
isVerified _ = False

isDischarged :: Path lang (EvaluationWitness lang) -> Bool
isDischarged Path {pathResult = Discharged} = True
isDischarged _ = False

isCounter :: Path lang (EvaluationWitness lang) -> Bool
isCounter Path {pathResult = CounterExample _ _} = True
isCounter _ = False

isCounterWith :: (Model -> Bool) -> Path lang (EvaluationWitness lang) -> Bool
isCounterWith f Path {pathResult = CounterExample _ m} = f m
isCounterWith f _ = False

isNoCounter :: Path lang (EvaluationWitness lang) -> Bool
isNoCounter = not . isCounter

-- *** Others

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False
