{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Language.Pirouette.PlutusIR.Common where

import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import qualified Data.Text.IO as T
import qualified Flat
import GHC.Float (rationalToDouble)
import qualified PlutusCore as P
import qualified PlutusCore.Flat as P
import PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser as PIR

openAndParsePIR ::
  FilePath ->
  IO (Program P.TyName P.Name P.DefaultUni P.DefaultFun PIR.SourcePos)
openAndParsePIR fileName = do
  !content <- T.readFile fileName
  case PIR.parse (PIR.program @P.DefaultUni @P.DefaultFun) fileName content of
    Left err -> print err >> error "Couldn't parse"
    Right p -> return p

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