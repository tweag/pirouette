{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Language.Pirouette.PlutusIR.SymEvalSpec where

import Control.Monad.Except ( runExcept )
import Control.Monad.Reader ( ReaderT(runReaderT) )
import Language.Pirouette.PlutusIR
import Language.Pirouette.PlutusIR.Syntax
import Language.Pirouette.PlutusIR.ToTerm
import Pirouette.Monad
import Pirouette.Symbolic.EvalUtils
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax
import Pirouette.Transformations (elimEvenOddMutRec)
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.Monomorphization
import PlutusCore (DefaultUni (..))
import qualified PlutusCore as P
import qualified PlutusCore.Pretty as P
import qualified PlutusIR.Core.Type as PIR

import Language.Pirouette.PlutusIR.Common (openAndParsePIR)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (expectFail)

execFromPIRFile ::
  (Problem PlutusIR -> ReaderT (PrtOrderedDefs PlutusIR) (PrtT IO) a) ->
  FilePath -> (Type PlutusIR, Term PlutusIR) ->
  (Term PlutusIR, Term PlutusIR) ->
  IO (Either String a)
execFromPIRFile toDo path (tyRes, fn) (assume, toProve) = do
  pir <- openAndParsePIR path
  exec toDo (pir, tyRes, fn) (assume, toProve)

exec ::
  (PIRConstraint tyname name P.DefaultFun, Show loc) =>
  (Problem PlutusIR -> ReaderT (PrtOrderedDefs PlutusIR) (PrtT IO) a) ->
  (PIR.Program tyname name DefaultUni P.DefaultFun loc, Type PlutusIR, Term PlutusIR) ->
  (Term PlutusIR, Term PlutusIR) ->
  IO (Either String a)
exec toDo (pirProgram, tyRes, fn) (assume, toProve) =
  case runExcept $ trProgram pirProgram of
    Left e -> pure (Left $ show e)
    Right (main, decls) ->
      fmap fst $ mockPrtT $ do
        orderedDecls <- elimEvenOddMutRec $ PrtUnorderedDefs decls main
        flip runReaderT orderedDecls $
          toDo (Problem tyRes fn assume toProve)

tests :: [TestTree]
tests =
  [ testGroup
      "simple triples"
      [ testCase "just evaluation" $ 
          execFromPIRFile proveUnbounded 
            "tests/unit/resources/fromPlutusIRSpec-01.pir"
            ( [pirTy| Bool |], [pir| \(x : Integer) . addone x |])
            ( [pir| \(result : Integer) (x : Integer) . 0 < result |],
              [pir| \(result : Integer) (x : Integer) . 0 < x |]
            )
            `pathSatisfies` (isSingleton .&. all isCounter)
      ]
  ]