{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Symbolic.ProveSpec.NastyLists (tests) where

import Control.Monad.Reader
import Data.Default
import Data.Maybe (isJust)
import Language.Pirouette.Example
import qualified Language.Pirouette.Example.IsUnity as IsUnity
import Language.Pirouette.Example.StdLib (stdLib)
import Pirouette.Monad
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.EvalUtils
import Pirouette.Symbolic.ProveSpec.Internal
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax
import Pirouette.Transformations (elimEvenOddMutRec)
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.EtaExpand
import Pirouette.Transformations.Monomorphization
import qualified PureSMT
import Test.Tasty
import Test.Tasty.HUnit

tests :: [TestTree]
tests =
  [ testCase "forall x l. elem x (Cons x l)" $
      exec
        (proveUnbounded def)
        (stdLib, [ty|Bool|], [term|\(x:Integer) (l:List Integer) . elem @Integer eqInteger x (Cons @Integer x l)|])
        ( [term|\(r:Bool) (x:Integer) (l:List Integer) . r|],
          [term|\(r:Bool) (x:Integer) (l:List Integer) . True|]
        )
        `pathSatisfies` (all isNoCounter .&. any isVerified)
  ]
