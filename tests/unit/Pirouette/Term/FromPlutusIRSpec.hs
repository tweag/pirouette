{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module Pirouette.Term.FromPlutusIRSpec where

import           Pirouette.Term.FromPlutusIR
import           Pirouette.Term.Syntax

import           PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser    as PIR
import qualified PlutusCore         as P

import           Data.Either           (isRight)
import qualified Data.Map           as M
import qualified Data.Text          as T
import qualified Data.Text.IO       as T
import           Text.Megaparsec.Error (errorBundlePretty)
import           Control.Monad.Except
import           Test.Hspec

openAndParsePIR :: FilePath
                -> IO (Program P.TyName P.Name P.DefaultUni P.DefaultFun PIR.SourcePos)
openAndParsePIR fileName = do
  content <- T.readFile fileName
  case PIR.parse (PIR.program @P.DefaultUni @P.DefaultFun) fileName content of
    Left err -> putStrLn (errorBundlePretty err) >> error "Couldn't parse"
    Right p  -> return p

spec = do
  mod <- runIO (openAndParsePIR "tests/unit/resources/fromPlutusIRSpec-01.pir")
  let mod' = runExcept (trProgram mod)

  describe "trProgram" $ do
    it "Translates the PIR program correctly" $
      isRight mod' `shouldBe` True

    let Right (_, decls) = mod'
    it "Correctly puts terms in NF" $
      case (,) <$> M.lookup (Name "long"  (Just 24)) decls
               <*> M.lookup (Name "short" (Just 25)) decls of
        Just (DFunction _ l _ , DFunction _ s _) -> l `shouldBe` s
        _                                        -> expectationFailure "long/short not declared"
