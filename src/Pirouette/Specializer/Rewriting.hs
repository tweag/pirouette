{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE OverloadedStrings    #-}

module Pirouette.Specializer.Rewriting where

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.FromPlutusIR

import qualified PlutusIR.Parser    as PIR
import qualified PlutusCore         as P

import           Control.Monad.Except

import qualified Data.Text          as T
import qualified Data.Text.IO       as T

data RewritingRule l r = RewritingRule {
  name :: T.Text,
  lhs  :: l,
  rhs  :: r
} deriving Show

parseFileTransfo :: (MonadIO m)
                 => FilePath -> m [RewritingRule PrtTerm PrtTerm]
parseFileTransfo fileName = do
  content <- liftIO $ T.readFile fileName
  let lines = T.lines content
  return $ map transfoOfOneLine lines

  where

    transfoOfOneLine :: T.Text -> RewritingRule PrtTerm PrtTerm
    transfoOfOneLine l =
      let [transfoName,def] = T.splitOn ":" l in
      let [lhsTxt,rhsTxt] = map T.strip $ T.splitOn "==>" def in
      let lhsPIR =
            either (error . show) id $
              PIR.parse
                (PIR.term @P.DefaultUni @P.DefaultFun)
                (T.unpack transfoName  ++ "-LEFT")
                lhsTxt
      in
      let lhs = either (error . show) id $
                  runExcept (trPIRTerm lhsPIR)
      in
      let rhsPIR =
            either (error . show) id $
              PIR.parse
                (PIR.term @P.DefaultUni @P.DefaultFun)
                (T.unpack transfoName ++ "-RIGHT")
                rhsTxt
      in
      let rhs = either (error . show) id $
                  runExcept (trPIRTerm rhsPIR)
      in RewritingRule transfoName lhs rhs
