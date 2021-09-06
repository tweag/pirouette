{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module Pirouette.Term.FromPlutusIRSpec where

import           Pirouette.Term.FromPlutusIR
import           Pirouette.Term.Syntax
import           Pirouette.Term.Transformations
import           Pirouette.Monad
import           Pirouette.Monad.Logger

import           PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser    as PIR
import qualified PlutusCore         as P

import           Data.Either           (isRight, fromRight)
import           Data.Maybe            (fromJust)
import qualified Data.Map           as M
import qualified Data.Text          as T
import qualified Data.Text.IO       as T
import           Text.Megaparsec.Error (errorBundlePretty)
import           Control.Monad.Except
import           Control.Monad.Identity
import           Test.Hspec
import           Debug.Trace

openAndParsePIR :: FilePath
                -> IO (Program P.TyName P.Name P.DefaultUni P.DefaultFun PIR.SourcePos)
openAndParsePIR fileName = do
  content <- T.readFile fileName
  case PIR.parse (PIR.program @P.DefaultUni @P.DefaultFun) fileName content of
    Left err -> putStrLn (errorBundlePretty err) >> error "Couldn't parse"
    Right p  -> return p

mockPrtLog :: Decls Name P.DefaultFun -> PrtT Identity a -> Either String a
mockPrtLog ds f =
  let (res, logs) = runIdentity $ mockPrtT ds f
   in trace (unlines $ map msgContent logs) res


spec = do
  mod <- runIO (openAndParsePIR "tests/unit/resources/fromPlutusIRSpec-01.pir")
  let mod' = runExcept (trProgramDecls mod)
  let Right decls = mod'
  let longN  = head $ filter ((== "long") . nameString) $ M.keys decls
  let shortN = head $ filter ((== "short") . nameString) $ M.keys decls

  describe "From PIR to PrtTerms" $ do
    it "Translates the PIR program without errors" $
      isRight mod' `shouldBe` True

    it "Constains 'long' and 'short' terms" $ do
      case (,) <$> M.lookup longN decls <*> M.lookup shortN decls of
        Just _  -> True `shouldBe` True
        Nothing -> expectationFailure "long/short not declared"

  let (DFunction _ long _)  = fromJust $ M.lookup longN  decls
  let (DFunction _ short _) = fromJust $ M.lookup shortN decls
  describe "PrtTerms Expansion" $ do
    it "Produces NF terms" $ do
      mockPrt decls (expandDefs long) `shouldBe` Right short
