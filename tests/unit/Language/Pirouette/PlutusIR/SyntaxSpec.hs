{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuasiQuotes #-}

module Language.Pirouette.PlutusIR.SyntaxSpec where

import Control.Monad.Except
import Data.Foldable (toList)
import GHC.Float (rationalToDouble)
import Language.Pirouette.PlutusIR
import Pirouette.Term.TypeChecker
import Pirouette.Term.Syntax.Pretty
import Pirouette.Term.Syntax.Base hiding (Program)
import qualified PlutusCore as P
import qualified PlutusCore.Pretty as P
import PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser as PIR
import Test.Tasty
import Test.Tasty.HUnit

import Language.Pirouette.PlutusIR.Common

goldenFiles :: [(String, FilePath)]
goldenFiles = [("Split", "tests/unit/resources/split.flat")
              ,("Auction", "tests/unit/resources/auction.flat")]

canParseTerm :: Term PlutusIR -> Assertion
canParseTerm _ = return ()

tests :: [TestTree]
tests =
  [ testGroup "Read, translate and typecheck programs" $ flip map goldenFiles $ \(n, fpath) ->
       testCase n (assertTrProgramOk fpath),
    testCase "Can parse terms" $ do
      canParseTerm [pir| \(x : Integer) . x + 1 |]
      canParseTerm [pir| \(bs : ByteString) . b/appendByteString bs bs |]
  ]

assertTrProgramOk :: FilePath -> Assertion
assertTrProgramOk flatFilePath = do
  Right pir <- openAndDecodeFlat flatFilePath
  case runExcept (trProgram pir) of
    Left err -> assertFailure $ "Translate program: " ++ show err
    Right (_, decls) -> do
      -- writeFile "decls.pirouette" (show $ pretty decls)
      case typeCheckDecls (builtinTypeDecls decls <> decls) of
        Left err -> assertFailure $ "Typecheck program: " ++ show (pretty err)
        Right _ -> return ()
  return ()
