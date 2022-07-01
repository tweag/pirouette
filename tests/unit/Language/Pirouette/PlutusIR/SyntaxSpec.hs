{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuasiQuotes #-}

module Language.Pirouette.PlutusIR.SyntaxSpec where

import Control.Monad.Except
import Data.Foldable (toList)
import Data.Map (keys)
import GHC.Float (rationalToDouble)
import Language.Pirouette.PlutusIR
import Language.Pirouette.PlutusIR.Common
import Pirouette.Monad
import Pirouette.Term.Syntax.Base hiding (Program)
import Pirouette.Term.Syntax.Pretty
import Pirouette.Term.TypeChecker
import qualified PlutusCore as P
import qualified PlutusCore.Pretty as P
import PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser as PIR
import Test.Tasty
import Test.Tasty.HUnit

goldenFiles :: [(String, FilePath)]
goldenFiles =
  [ ("Split", "tests/unit/resources/split.flat"),
    ("Auction", "tests/unit/resources/auction.flat")
  ]

canParseTerm :: Term PlutusIR -> Assertion
canParseTerm _ = return ()

tests :: [TestTree]
tests =
  [ testGroup "Read, translate and typecheck programs" $
      flip map goldenFiles $ \(n, fpath) ->
        testCase n (assertTrProgramOk fpath),
    testCase "Can parse terms" $ do
      canParseTerm [pir| \(x : Integer) . x + 1 |]
      canParseTerm [pir| \(bs : ByteString) . b/appendByteString bs bs |]
  ]

assertTrProgramOk :: FilePath -> Assertion
assertTrProgramOk flatFilePath = do
  (_, PrtUnorderedDefs decls) <- openAndDecodeFlat flatFilePath
  -- writeFile "decls.pirouette" (show $ pretty decls)
  let allDecls = builtinTypeDecls decls <> decls
  -- print $ pretty allDecls
  case typeCheckDecls allDecls of
    Left err -> assertFailure $ "Typecheck program: " ++ show (pretty err)
    Right _ -> return ()
  return ()
