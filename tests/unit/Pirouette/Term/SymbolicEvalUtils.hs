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

(.&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p .&. q = \x -> p x && q x

isVerified, isDischarged, isCounter, isNoCounter :: Path lang (EvaluationWitness lang) -> Bool

isVerified Path { pathResult = Verified } = True
isVerified _ = False

isDischarged Path { pathResult = Discharged } = True
isDischarged _ = False

isCounter Path { pathResult = CounterExample _ _ } = True
isCounter _ = False

isNoCounter = not . isCounter

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False