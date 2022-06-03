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
import qualified PlutusCore as P
import qualified PlutusCore.Flat as P
import qualified PlutusCore.Pretty as P
import PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser as PIR
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (expectFail)

splitFilePath :: FilePath
splitFilePath = "tests/unit/resources/split.flat"

auctionFilePath :: FilePath
auctionFilePath = "tests/unit/resources/auction.flat"

tests :: [TestTree]
tests =
  [ testGroup
      "PIR validators typecheck"
      [ testCase "The split validator typechecks" (assertTrProgram splitFilePath),
        testCase "The auction validator typechecks" (assertTrProgram auctionFilePath)
      ]
  ]

assertTrProgram :: FilePath -> Assertion
assertTrProgram flatFilePath = do
  Right (Showable pir) <- openAndDecodeFlat flatFilePath
  case runExcept (trProgram pir) of
    Left err -> assertFailure $ "Translate program: " ++ show err
    Right (_, decls) -> return ()
  return ()

data Showable (f :: * -> *) :: * where
  Showable :: (Show x) => f x -> Showable f

openAndDecodeFlat ::
  (MonadIO m) =>
  FilePath ->
  m (Either String (Showable (Program P.TyName P.Name P.DefaultUni P.DefaultFun)))
openAndDecodeFlat fileName = do
  content <- liftIO $ BS.readFile fileName
  return . either (Left . show) (Right . Showable) $
    pirDecoder content
  where
    pirDecoder :: BS.ByteString -> Flat.Decoded (Program P.TyName P.Name P.DefaultUni P.DefaultFun ())
    pirDecoder = Flat.unflat
