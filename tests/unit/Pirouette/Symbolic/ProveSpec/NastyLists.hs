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
        ( stdLib,
          [ty|Bool|],
          [term|\(x:Integer) (l:List Integer) .
                  elem @Integer eqInteger x (Cons @Integer x l)|]
        )
        ( [term|\(r:Bool) (x:Integer) (l:List Integer) . r|],
          [term|\(r:Bool) (x:Integer) (l:List Integer) . True|]
        )
        `pathSatisfies` (all isNoCounter .&. any isVerified),
    testCase "not (forall l. elem 0 l)" $
      exec
        (prove def)
        ( stdLib,
          [ty|Bool|],
          [term|\(l:List Integer) . elem @Integer eqInteger 0 l|]
        )
        ( [term|\(r:Bool) (l:List Integer) . not r|],
          [term|\(r:Bool) (l:List Integer) . True|]
        )
        `pathSatisfies` any isCounter,
    testCase "forall x l. elem x (append l [x])" $
      exec
        (proveBounded def 25) -- fuel heuristically chosen to not take too long
        ( stdLib,
          [ty|Bool|],
          [term|\(x:Integer) (l:List Integer) .
                  elem @Integer eqInteger x (append @Integer l (Cons @Integer x (Nil @Integer)))|]
        )
        ( [term|\(r:Bool) (x:Integer) (l:List Integer) . r|],
          [term|\(r:Bool) (x:Integer) (l:List Integer) . True|]
        )
        `pathSatisfies` ( all (stillHasFuel .=>. isNoCounter)
                            .&. any (stillHasFuel .&. isVerified)
                        )
                        -- NOTE: We really need this predicate `stillHasFuel .=> isNoCounter` here
                        -- because paths that run out of fuel are also considered counter-example
                        -- but we do not want those paths to make the test fail. The predicate
                        -- `stillHasFuel .&. isVerified` is overkill as `isVerified` would
                        -- probably be enough, but we find this version clearer.
  ]
