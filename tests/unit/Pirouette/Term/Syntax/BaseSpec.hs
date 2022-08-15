{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Pirouette.Term.Syntax.BaseSpec (tests) where

import Data.String (fromString)
import Language.Pirouette.Example
import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Test.Tasty
import Test.Tasty.HUnit

either3Def :: TypeDef Ex
either3Def =
  Datatype
    { kind = SystF.KTo SystF.KStar (SystF.KTo SystF.KStar (SystF.KTo SystF.KStar SystF.KStar)),
      typeVariables = [("a", SystF.KStar), ("b", SystF.KStar), ("c", SystF.KStar)],
      destructor = "match_Either3",
      constructors =
        [ ("Left", [ty| forall a b c . a -> Either3 a b c |]),
          ("Mid", [ty| forall a b c . b -> Either3 a b c |]),
          ("Right", [ty| forall a b c . c -> Either3 a b c |])
        ]
    }

tests :: [TestTree]
tests =
  [ testCase "destructorTypeFor Either3" $
      destructorTypeFor (fromString "Either3") either3Def
        @?= [ty| forall a b c
             . Either3 a b c -> forall r . (a -> r) -> (b -> r) -> (c -> r) -> r |]
  ]
