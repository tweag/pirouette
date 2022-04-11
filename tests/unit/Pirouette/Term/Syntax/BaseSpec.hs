{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
module Pirouette.Term.Syntax.BaseSpec (tests) where

import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Language.Pirouette.Example
import Test.Tasty
import Test.Tasty.HUnit
import Data.String (fromString)

either3Def :: TypeDef Ex
either3Def =
  Datatype
    { kind = SystF.KTo SystF.KStar (SystF.KTo SystF.KStar (SystF.KTo SystF.KStar SystF.KStar)),
      typeVariables = [("a", SystF.KStar), ("b", SystF.KStar), ("c", SystF.KStar)],
      destructor = "match_Either3",
      constructors =
        [ ("Left", [ty| all (a : Type) (b : Type) (c : Type) . a -> Either3 a b c |]),
          ("Mid", [ty| all (a : Type) (b : Type) (c : Type) . b -> Either3 a b c |]),
          ("Right", [ty| all (a : Type) (b : Type) (c : Type) . c -> Either3 a b c |])
        ]
    }

tests :: [TestTree]
tests =
  [ testCase "destructorTypeFor Either3" $
      destructorTypeFor (fromString "Either3") either3Def @?=
        [ty| all (a : Type) (b : Type) (c : Type)
             . Either3 a b c -> all (r : Type) . (a -> r) -> (b -> r) -> (c -> r) -> r |]
  ]
