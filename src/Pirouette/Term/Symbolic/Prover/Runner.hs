{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Pirouette.Term.Symbolic.Prover.Runner where

import Control.Monad.Reader
import Pirouette.Monad
import Pirouette.SMT
import Pirouette.Term.Symbolic.Eval
import Pirouette.Term.Symbolic.Prover
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.Pretty.Class
import Pirouette.Term.Syntax.SystemF (tyFunArgs)
import Pirouette.Term.TypeChecker
import Pirouette.Transformations
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.Monomorphization
import System.Console.ANSI

data AssumeProve lang = Term lang :==>: Term lang
  deriving (Eq, Show)

incorrectnessLogic ::
  (LanguagePretty lang, LanguageBuiltinTypes lang, LanguageSMTBranches lang) =>
  Int ->
  Program lang ->
  Term lang ->
  AssumeProve lang ->
  IO ()
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
  where
    isCounter Path {pathResult = CounterExample _ _} = True
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
  print $ pretty model
printResult steps (Right _) = do
  setSGR [SetColor Foreground Vivid Green]
  putStrLn $ "✔️ NO COUNTEREXAMPLES FOUND AFTER " <> show steps <> " STEPS"
  setSGR [Reset]
