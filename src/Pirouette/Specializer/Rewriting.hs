{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Pirouette.Specializer.Rewriting where

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.FromPlutusIR

import qualified PlutusIR.Parser    as PIR
import qualified PlutusCore         as P

import           Control.Monad.Except

import Data.Bifunctor
import qualified Data.Text           as T

data RewritingRule l r = RewritingRule {
  name :: T.Text,
  lhs  :: l,
  rhs  :: r
} deriving Show

instance Bifunctor RewritingRule where
  bimap f g (RewritingRule name l r) = RewritingRule name (f l) (g r)


parseRewRule :: RewritingRule T.Text T.Text -> RewritingRule PrtTerm PrtTerm
parseRewRule r@(RewritingRule n _ _) =
  bimap (parse (T.unpack n ++ "-LEFT")) (parse (T.unpack n ++ "-RIGHT")) r

  where

    parse :: String -> T.Text -> PrtTerm
    parse err t =
      let tPIR =
            either (error . show) id $
              PIR.parse (PIR.term @P.DefaultUni @P.DefaultFun) err t
      in
      either (error . show) id $ runExcept (trPIRTerm tPIR)