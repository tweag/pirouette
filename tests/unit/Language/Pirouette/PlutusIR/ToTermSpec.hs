{-# LANGUAGE OverloadedStrings #-}

module Language.Pirouette.PlutusIR.ToTermSpec where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Debug.Trace
import Language.Pirouette.PlutusIR.Common
import Language.Pirouette.PlutusIR.ToTerm
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Transformations
import Test.Tasty
import Test.Tasty.HUnit

tests :: [TestTree]
tests = (: []) $
  withResource acquire (const $ return ()) $ \progAct ->
    testGroup
      "With resource: tests/unit/resources/fromPlutusIRSpec-01.pir"
      [ testCase "Translates the PIR program without errors" $ do
          -- We force a pattern match on at least one declaration, which
          -- means that translation had to happen at this point.
          _ : _ <- M.toList <$> progAct
          return (),
        -- Test that two declarations are present
        testCase "Decls contain 'long' and 'short' terms" $ do
          decls <- progAct
          let longN = head $ filter ((== "long") . nameString . snd) $ M.keys decls
          let shortN = head $ filter ((== "short") . nameString . snd) $ M.keys decls
          case (,) <$> M.lookup longN decls <*> M.lookup shortN decls of
            Just _ -> return ()
            Nothing -> assertFailure "long/short not declared",
        -- Test that expanding one declaration yields the other declaration
        testCase "expandDefs produces NF terms" $ do
          decls <- progAct
          let longN = head $ filter ((== "long") . nameString . snd) $ M.keys decls
          let shortN = head $ filter ((== "short") . nameString . snd) $ M.keys decls
          let (DFunction _ long _) = fromJust $ M.lookup longN decls
          let (DFunction _ short _) = fromJust $ M.lookup shortN decls
          runReader (expandDefs long) (mocked decls) @?= short
      ]
  where
    mocked = flip PrtUnorderedDefs undefined
    acquire = do
      PrtUnorderedDefs decls _ <- openAndParsePIR "tests/unit/resources/fromPlutusIRSpec-01.pir"
      return decls

-- TODO: Check that Datatype decls have the typeVariables redeclared on
-- constructors
