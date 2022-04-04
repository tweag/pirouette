{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Pirouette.Specializer.Rewriting where

import Control.Monad.Except
import Data.Bifunctor
import qualified Data.Text as T
import Language.Pirouette.PlutusIR.Builtins
import Language.Pirouette.PlutusIR.ToTerm
import Pirouette.Term.Syntax.Base (Term)
import qualified PlutusCore as P
import qualified PlutusIR.Parser as PIR

data RewritingRule l r = RewritingRule
  { name :: T.Text,
    lhs :: l,
    rhs :: r
  }
  deriving (Show)

instance Bifunctor RewritingRule where
  bimap f g (RewritingRule nm l r) = RewritingRule nm (f l) (g r)

parseRewRule :: RewritingRule T.Text T.Text -> RewritingRule (Term BuiltinsOfPIR) (Term BuiltinsOfPIR)
parseRewRule r@(RewritingRule n _ _) =
  bimap (parse (T.unpack n ++ "-LEFT")) (parse (T.unpack n ++ "-RIGHT")) r
  where
    parse :: String -> T.Text -> Term BuiltinsOfPIR
    parse err t =
      let tPIR =
            either (error . show) id $
              PIR.parse (PIR.term @P.DefaultUni @P.DefaultFun) err t
       in either (error . show) id $ runExcept (trPIRTerm tPIR)
