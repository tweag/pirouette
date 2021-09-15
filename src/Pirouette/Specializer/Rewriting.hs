{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module Pirouette.Specializer.Rewriting where

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.FromPlutusIR

import qualified PlutusIR.Parser    as PIR
import qualified PlutusCore         as P

import           Control.Monad.Except
import Language.Haskell.TH
import System.Directory
import System.FilePath

import Data.Functor
import qualified Data.Text           as T
import qualified Data.Text.IO        as T
import qualified Data.Yaml           as Yaml
import qualified Data.HashMap.Strict as HM

data RewritingRule l r = RewritingRule {
  name :: T.Text,
  lhs  :: l,
  rhs  :: r
} deriving Show

transfoFilePath :: String
transfoFilePath = takeDirectory $(do
    dir <- runIO getCurrentDirectory
    filename <- loc_filename <$> location
    litE $ stringL $ dir </> filename) ++ "/PIR-transformations.spz"

parseFileTransfo :: (MonadIO m)
                 => FilePath -> m [RewritingRule PrtTerm PrtTerm]
parseFileTransfo fileName = do
  v <- Yaml.decodeFileThrow fileName
  let res = Yaml.parseEither yamlObjToRewRules v
  either (error . show) return res

  where

    yamlObjToRewRules :: Yaml.Value -> Yaml.Parser [RewritingRule PrtTerm PrtTerm]
    yamlObjToRewRules (Yaml.Object o) =
      sequence $ reverse $ HM.foldMapWithKey extractOneRewRule o

    extractOneRewRule :: T.Text -> Yaml.Value
                      -> [Yaml.Parser (RewritingRule PrtTerm PrtTerm)]
    extractOneRewRule k (Yaml.Object i) =
      [RewritingRule k <$>
        (parse (T.unpack k ++ "-LEFT") <$> i Yaml..: "lhs") <*>
        (parse (T.unpack k ++ "-RIGHT") <$> i Yaml..: "rhs")]

    parse :: String -> T.Text -> PrtTerm
    parse err t =
      let tPIR =
            either (error . show) id $
              PIR.parse (PIR.term @P.DefaultUni @P.DefaultFun) err t
      in
      either (error . show) id $ runExcept (trPIRTerm tPIR)