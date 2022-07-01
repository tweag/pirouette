{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Language.Pirouette.PlutusIR.SymEvalSpec where

import Control.Monad.Except (runExcept)
import Control.Monad.Reader (ReaderT (runReaderT))
import qualified Data.Map as M
import Language.Pirouette.PlutusIR
import Language.Pirouette.PlutusIR.Common (openAndParsePIR)
import Language.Pirouette.PlutusIR.Syntax
import Language.Pirouette.PlutusIR.ToTerm
import Pirouette
import Pirouette.Monad
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.EvalUtils
import Pirouette.Symbolic.Prover
import Pirouette.Symbolic.Prover.Runner
import Pirouette.Term.Syntax
import PlutusCore (DefaultUni (..))
import qualified PlutusCore as P
import qualified PlutusCore.Pretty as P
import qualified PlutusIR.Core.Type as PIR
import Test.Tasty
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.HUnit

execFromPIRFile ::
  FilePath -> IncorrectnessParams PlutusIR -> IO [Path PlutusIR (EvaluationWitness PlutusIR)]
execFromPIRFile path problem = do
  (_pirMain, pirDecls) <- openAndParsePIR path
  execIncorrectnessLogic proveUnbounded pirDecls problem

tests :: [TestTree]
tests =
  [ testGroup
      "simple triples"
      [ testCase "[input > 0] add 1 [result > 0] counter" $
          execFromPIRFile
            "tests/unit/resources/fromPlutusIRSpec-01.pir"
            ( IncorrectnessParams
                { ipTarget = [pir| \(x : Integer) . addone x |],
                  ipTargetType = [pirTy| Integer |],
                  ipCondition =
                    [pir| \(result : Integer) (x : Integer) . 0 < result |]
                      :==>: [pir| \(result : Integer) (x : Integer) . 0 < x |]
                }
            )
            `pathSatisfies` (isSingleton .&. all isCounter),
        testCase "[input > 0] add 1 [result > 1] verified" $
          execFromPIRFile
            "tests/unit/resources/fromPlutusIRSpec-01.pir"
            ( IncorrectnessParams
                { ipTarget = [pir| \(x : Integer) . addone x |],
                  ipTargetType = [pirTy| Integer |],
                  ipCondition =
                    [pir| \(result : Integer) (x : Integer) . 1 < result |]
                      :==>: [pir| \(result : Integer) (x : Integer) . 0 < x |]
                }
            )
            `pathSatisfies` (isSingleton .&. all isVerified)
      ]
  ]
