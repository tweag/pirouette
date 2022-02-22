{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Pirouette.Specializer.Rewriting where

import Pirouette.Term.Syntax.Base (Term)
import Pirouette.PlutusIR.ToTerm

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


parseRewRule :: RewritingRule T.Text T.Text -> RewritingRule (Term BuiltinsOfPIR) (Term BuiltinsOfPIR)
parseRewRule r@(RewritingRule n _ _) =
  bimap (parse (T.unpack n ++ "-LEFT")) (parse (T.unpack n ++ "-RIGHT")) r

  where

    parse :: String -> T.Text -> Term BuiltinsOfPIR
    parse err t =
      let tPIR =
            either (error . show) id $
              PIR.parse (PIR.term @P.DefaultUni @P.DefaultFun) err t
      in
      either (error . show) id $ runExcept (trPIRTerm tPIR)
