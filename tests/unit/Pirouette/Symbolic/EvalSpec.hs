{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Symbolic.EvalSpec (tests) where

import Control.Monad.Reader
import Language.Pirouette.Example
import Pirouette.Monad
import qualified Pirouette.SMT.Constraints as SMT
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.EvalUtils
import Pirouette.Term.Syntax.Base
import Pirouette.Transformations (elimEvenOddMutRec)
import qualified PureSMT as SMT
import Test.Tasty
import Test.Tasty.HUnit

-- TODO: write tests!
tests :: [TestTree]
tests = []
