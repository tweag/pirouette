{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Language.Pirouette.PlutusIR.BuiltinsSpec where

import Control.Monad
import Control.Monad.Except
import qualified Data.ByteString as BS
import qualified Flat
import GHC.Float (rationalToDouble)
import Language.Pirouette.PlutusIR.ToTerm
import Pirouette.Term.TypeChecker
import Pirouette.Term.Syntax.Pretty
import qualified PlutusCore as P
import qualified PlutusCore.Flat as P
import qualified PlutusCore.Pretty as P
import PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser as PIR
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (expectFail)

goldenFiles :: [(String, FilePath)]
goldenFiles = [("Split", "tests/unit/resources/split.flat")
              ,("Auction", "tests/unit/resources/auction.flat")]

tests :: [TestTree]
tests =
  [ testGroup "Read, translate and typecheck programs" $ flip map goldenFiles $ \(n, fpath) ->
       testCase n (assertTrProgramOk fpath)
  ]

assertTrProgramOk :: FilePath -> Assertion
assertTrProgramOk flatFilePath = do
  Right pir <- openAndDecodeFlat flatFilePath
  case runExcept (trProgram pir) of
    Left err -> assertFailure $ "Translate program: " ++ show err
    Right (_, decls) -> do
      -- writeFile "decls.pirouette" (show $ pretty decls)
      case typeCheckDecls decls of
        Left err -> assertFailure $ "Typecheck program: " ++ show (pretty err)
        Right _ -> return ()
  return ()

openAndDecodeFlat ::
  (MonadIO m) =>
  FilePath ->
  m (Either String (Program P.TyName P.Name P.DefaultUni P.DefaultFun ()))
openAndDecodeFlat fileName = do
  content <- liftIO $ BS.readFile fileName
  return . either (Left . show) Right $ pirDecoder content
  where
    pirDecoder :: BS.ByteString -> Flat.Decoded (Program P.TyName P.Name P.DefaultUni P.DefaultFun ())
    pirDecoder = Flat.unflat
