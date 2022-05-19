{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Pirouette.Term.Symbolic.Prover.Runner where

import Control.Monad.Reader
import Pirouette.Monad
import Pirouette.SMT
import Pirouette.Term.Symbolic.Eval
import Pirouette.Term.Symbolic.Prover
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF (tyFunArgs)
import Pirouette.Term.TypeChecker
import Pirouette.Transformations
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.Monomorphization
import System.Console.ANSI
import qualified Test.Tasty.HUnit as Test

data AssumeProve lang = Term lang :==>: Term lang
  deriving (Eq, Show)

incorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSMTBranches lang) =>
  Int ->
  Program lang ->
  Term lang ->
  AssumeProve lang ->
  Test.Assertion
incorrectnessLogic fuel program validator (post :==>: pre) = do
  (result, _logs) <- mockPrtT $ do
    let prog0 = uncurry PrtUnorderedDefs program
    let prog1 = monomorphize prog0
    let decls = defunctionalize prog1
    orderedDecls <- elimEvenOddMutRec decls
    let Right (Just (_, resultTy)) =
          fmap (fmap tyFunArgs) $
            flip runReaderT ((prtDecls orderedDecls, []), [DeclPath "validator"]) $
              typeInferTerm validator
    flip runReaderT orderedDecls $ do
      proveAnyWithFuel fuel isCounter (Problem resultTy validator post pre)
  printResult fuel result
  assertAllClear result
  where
    isCounter Path {pathResult = CounterExample _ _, pathStatus = s}
      | s /= OutOfFuel = True
    isCounter _ = False

printResult ::
  Int ->
  Either String (Maybe (Path lang (EvaluationWitness lang))) ->
  IO ()
printResult _ (Left e) = do
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "UNEXPECTED ERROR"
  setSGR [Reset]
  putStrLn e
printResult _ (Right (Just Path {pathResult = CounterExample _ model})) = do
  setSGR [SetColor Foreground Vivid Yellow]
  putStrLn "💸 COUNTEREXAMPLE FOUND"
  setSGR [Reset]
  print $ showModelHaskellish model
printResult steps (Right _) = do
  setSGR [SetColor Foreground Vivid Green]
  putStrLn $ "✔️ NO COUNTEREXAMPLES FOUND AFTER " <> show steps <> " STEPS"
  setSGR [Reset]

-- | Assert a test failure (Tasty HUnit integration) when the result of the
-- incorrectness logic execution reveals an error or a counterexample.
assertAllClear ::
  Either String (Maybe (Path lang (EvaluationWitness lang))) ->
  Test.Assertion
assertAllClear (Left _) = Test.assertFailure "Unexpected error"
assertAllClear (Right (Just Path {pathResult = CounterExample _ _})) =
  Test.assertFailure "Counterexample found"
assertAllClear (Right _) = return ()
