{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

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

type IncorrectnessResult lang =
  Either String (Maybe (Path lang (EvaluationWitness lang)))

-- | Parameters for an incorrectness logic run
data IncorrectnessParams lang = IncorrectnessParams
  { ipDefinitions :: Program lang,
    ipTarget :: Term lang,
    ipCondition :: AssumeProve lang,
    ipMaxCstrs :: Int
  }

runIncorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSMTBranches lang) =>
  IncorrectnessParams lang ->
  IO (IncorrectnessResult lang)
runIncorrectnessLogic
  (IncorrectnessParams definitions target (post :==>: pre) maxCstrs) = do
    let shouldStop = \st -> sestConstructors st > maxCstrs
    (result, _logs) <- mockPrtT $ do
      let prog0 = uncurry PrtUnorderedDefs definitions
      let prog1 = monomorphize prog0
      let decls = defunctionalize prog1
      orderedDecls <- elimEvenOddMutRec decls
      let Right (Just (_, resultTy)) =
            fmap (fmap tyFunArgs) $
              flip runReaderT ((prtDecls orderedDecls, []), [DeclPath "validator"]) $
                typeInferTerm target
      flip runReaderT orderedDecls $ do
        proveAny shouldStop isCounter (Problem resultTy target post pre)
    return result
    where
      isCounter Path {pathResult = CounterExample _ _, pathStatus = s}
        | s /= OutOfFuel = True
      isCounter _ = False

printIRResult ::
  Int ->
  IncorrectnessResult lang ->
  IO ()
printIRResult _ (Left e) = do
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "UNEXPECTED ERROR"
  setSGR [Reset]
  putStrLn e
printIRResult _ (Right (Just Path {pathResult = CounterExample _ model})) = do
  setSGR [SetColor Foreground Vivid Yellow]
  putStrLn "💸 COUNTEREXAMPLE FOUND"
  setSGR [Reset]
  print $ showModelHaskellish model
printIRResult steps (Right _) = do
  setSGR [SetColor Foreground Vivid Green]
  putStrLn $ "✔️ NO COUNTEREXAMPLES FOUND AFTER " <> show steps <> " STEPS"
  setSGR [Reset]

assertIRResult :: IncorrectnessResult lang -> Test.Assertion
assertIRResult (Left _) = Test.assertFailure "Unexpected error"
assertIRResult (Right (Just Path {pathResult = CounterExample _ _})) =
  Test.assertFailure "Counterexample found"
assertIRResult (Right _) = return ()

-- | Check for counterexamples for an incorrectness logic triple and
-- pretty-print the result
replIncorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSMTBranches lang) =>
  IncorrectnessParams lang ->
  IO ()
replIncorrectnessLogic params@IncorrectnessParams {..} =
  runIncorrectnessLogic params >>= printIRResult ipMaxCstrs

-- | Assert a test failure (Tasty HUnit integration) when the result of the
-- incorrectness logic execution reveals an error or a counterexample.
assertIncorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSMTBranches lang) =>
  IncorrectnessParams lang ->
  Test.Assertion
assertIncorrectnessLogic params =
  runIncorrectnessLogic params >>= assertIRResult
