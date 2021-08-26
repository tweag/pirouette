{-# LANGUAGE OverloadedStrings #-}
module Pirouette.Term.Syntax.SystemFSpec (spec) where

import Pirouette.Term.Syntax.SystemF hiding (tyApp)

import Data.List (groupBy, transpose)
import Control.Arrow (first)

import           Control.Monad
import           Data.Text.Prettyprint.Doc
import           Test.Hspec

type Ty = Type (Var String String)

tyApp :: Ty -> Ty -> Ty
tyApp = app

spec = do
  describe "type-level appN" $ do
    it "works for hand-crafted examples" $
      tyApp (TyLam "x" KStar $ TyApp (B "y" 1) [tyPure $ B "x" 0])
            (TyLam "w" KStar $ TyApp (B "z" 2) [tyPure $ B "w" 0])
          `shouldBe`
      tyApp (tyPure $ B "y" 0)
            (TyLam "w" KStar $ TyApp (B "z" 2) [tyPure $ B "w" 0])
