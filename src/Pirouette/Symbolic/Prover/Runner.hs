{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Pirouette.Symbolic.Prover.Runner where

import Control.Monad.Reader
import Pirouette.Monad
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax (pretty)
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF (tyFunArgs)
import Pirouette.Term.TypeChecker
import Pirouette.Transformations
import System.Console.ANSI
import qualified Test.Tasty.HUnit as Test

data AssumeProve lang = Term lang :==>: Term lang
  deriving (Eq, Show)

type IncorrectnessResult lang = Maybe (Path lang (EvaluationWitness lang))

-- | Parameters for an incorrectness logic run
data IncorrectnessParams lang = IncorrectnessParams
  { ipDefinitions :: Program lang,
    ipTarget :: Term lang,
    ipCondition :: AssumeProve lang,
    ipMaxCstrs :: Int
  }

runIncorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSymEval lang) =>
  IncorrectnessParams lang ->
  IncorrectnessResult lang
runIncorrectnessLogic
  (IncorrectnessParams definitions target (post :==>: pre) maxCstrs) = do
    let shouldStop = \st -> sestConstructors st > maxCstrs
    let prog0 = uncurry PrtUnorderedDefs definitions
    let prog1 = monomorphize prog0
    let decls = defunctionalize prog1
    let orderedDecls = elimEvenOddMutRec decls
    let Right (Just (_, resultTy)) =
          fmap (fmap tyFunArgs) $
            flip runReaderT ((prtDecls orderedDecls, []), [DeclPath "validator"]) $
              typeInferTerm target
    flip runReader orderedDecls $ do
      proveAny shouldStop isCounterExample (Problem resultTy target post pre)
    where
      isCounterExample Path {pathResult = CounterExample _ _, pathStatus = s}
        | s /= OutOfFuel = True
      isCounterExample _ = False

printIRResult ::
  Int ->
  IncorrectnessResult lang ->
  IO ()
printIRResult _ (Just Path {pathResult = CounterExample _ model}) = do
  setSGR [SetColor Foreground Vivid Yellow]
  putStrLn "💸 COUNTEREXAMPLE FOUND"
  setSGR [Reset]
  print $ pretty model
printIRResult steps _ = do
  setSGR [SetColor Foreground Vivid Green]
  putStrLn $ "✔️ NO COUNTEREXAMPLES FOUND AFTER " <> show steps <> " STEPS"
  setSGR [Reset]

assertIRResult :: IncorrectnessResult lang -> Test.Assertion
assertIRResult (Just Path {pathResult = CounterExample _ _}) =
  Test.assertFailure "Counterexample found"
assertIRResult _ = return ()

-- | Check for counterexamples for an incorrectness logic triple and
-- pretty-print the result
replIncorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSymEval lang) =>
  IncorrectnessParams lang ->
  IO ()
replIncorrectnessLogic params@IncorrectnessParams {..} =
  printIRResult ipMaxCstrs (runIncorrectnessLogic params)

-- | Assert a test failure (Tasty HUnit integration) when the result of the
-- incorrectness logic execution reveals an error or a counterexample.
assertIncorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSymEval lang) =>
  IncorrectnessParams lang ->
  Test.Assertion
assertIncorrectnessLogic params =
  assertIRResult (runIncorrectnessLogic params)
