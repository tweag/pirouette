{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Control.Monad.Reader
import Data.Default
import Data.Maybe (isJust)
import qualified Debug.TimeStats as TimeStats
import Language.Pirouette.Example
import qualified Language.Pirouette.Example.IsUnity as IsUnity
import Pirouette.Monad
-------------------- Utils --------------------
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax
import Pirouette.Transformations (elimEvenOddMutRec)
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.Monomorphization
import Prettyprinter (vsep)
import Test.Tasty.HUnit

(*=*) :: (Eq a, Show a) => IO (Either String a) -> a -> Assertion
thing *=* expected = do
  given <- thing
  case given of
    Left e -> assertFailure $ "finished with errors: " <> e
    Right x -> x @=? expected

satisfies ::
  Show a =>
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
  assertBool ("property not satisfied:\n" <> show (vsep $ map pretty paths)) (property paths)

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
isCounterWith _f _ = False

isNoCounter = not . isCounter

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False

------------------------------------------------------------

isUnity :: (PrtUnorderedDefs Ex, Type Ex, Term Ex)
isUnity =
  ( IsUnity.definitions,
    [ty|Bool|],
    [term| \(tx : TxInfo) . validator tx |]
  )

-- Now we estabilish the incorrectness triple that says:
--
-- > [ \v -> correct_isUnity example_ac v ] validator v [ \r _ -> r ]
--
-- In other words, it only validates if @v@ is correct. We expect
-- a counterexample out of this.
condIsUnity :: (Term Ex, Term Ex)
condIsUnity =
  ( [term| \(result : Bool) (tx : TxInfo) . result |],
    [term| \(result : Bool) (tx : TxInfo) . correct_validator tx |]
  )

execFull ::
  (Problem Ex -> ReaderT (PrtOrderedDefs Ex) IO a) ->
  (PrtUnorderedDefs Ex, Type Ex, Term Ex) ->
  (Term Ex, Term Ex) ->
  IO a
execFull toDo (prog0, tyRes, fn) (assume, toProve) = do
  let prog1 = monomorphize prog0
  let decls = defunctionalize prog1
  let orderedDecls = elimEvenOddMutRec decls
  flip runReaderT orderedDecls $
    toDo (Problem tyRes fn assume toProve)

main :: IO ()
main =
  do
    _ <-
      TimeStats.measureM "main" $
        replicateM 100 $
          execFull (proveAny def isCounter) isUnity condIsUnity `satisfies` isJust
    TimeStats.printTimeStats
