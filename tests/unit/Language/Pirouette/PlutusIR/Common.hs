{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Language.Pirouette.PlutusIR.Common where

import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import qualified Data.Text.IO as T
import qualified Flat
import GHC.Float (rationalToDouble)
import Language.Pirouette.PlutusIR.Syntax
import Language.Pirouette.PlutusIR.ToTerm
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified PlutusCore as P
import qualified PlutusCore.Flat as P
import qualified PlutusIR.Core.Type as PIR (Program)
import qualified PlutusIR.Parser as PIR

openAndParsePIR :: FilePath -> IO (Term PlutusIR, PrtUnorderedDefs PlutusIR)
openAndParsePIR fileName = openAndDecodeWith T.readFile pirParser fileName
  where
    pirParser = PIR.parse (PIR.program @P.DefaultUni @P.DefaultFun) fileName

openAndDecodeFlat :: FilePath -> IO (Term PlutusIR, PrtUnorderedDefs PlutusIR)
openAndDecodeFlat = openAndDecodeWith BS.readFile pirDecoder
  where
    pirDecoder :: BS.ByteString -> Flat.Decoded (PIR.Program P.TyName P.Name P.DefaultUni P.DefaultFun ())
    pirDecoder = Flat.unflat

-- | Returns the decoded main term and the context of unordered definitions.
openAndDecodeWith ::
  (Show err, Show loc) =>
  (FilePath -> IO content) ->
  (content -> Either err (PIR.Program P.TyName P.Name P.DefaultUni P.DefaultFun loc)) ->
  FilePath ->
  IO (Term PlutusIR, PrtUnorderedDefs PlutusIR)
openAndDecodeWith read decoder fileName = do
  !content <- read fileName
  case decoder content of
    Left err -> print err >> error "Coult not decode"
    Right pirProgram ->
      let Right (main, decls) = runExcept $ trProgram pirProgram
       in return (main, PrtUnorderedDefs decls)
