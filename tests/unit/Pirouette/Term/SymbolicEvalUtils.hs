module Pirouette.Term.SymbolicEvalUtils where

import Pirouette.Term.Syntax.Base
import Pirouette.Term.Symbolic.Eval
import Test.Tasty.HUnit

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

pathSatisfies :: (LanguageBuiltins lang, Show res) => IO (Either String [Path lang res]) -> ([Path lang res] -> Bool) -> Assertion
thing `pathSatisfies` property = do
  given <- thing
  case given of
    Left e -> assertFailure $ "finished with errors: " <> e
    Right paths -> assertBool ("property not satisfied: " <> show paths) (property paths)

singleVerified :: [Path lang (EvaluationWitness lang)] -> Bool
singleVerified [Path { pathResult = Verified }] = True
singleVerified _ = False

singleCounter :: [Path lang (EvaluationWitness lang)] -> Bool
singleCounter [Path { pathResult = CounterExample _ }] = True
singleCounter _ = False 

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False