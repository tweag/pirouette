{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Pirouette.Term.TransformationsSpec (spec) where

import           Pirouette.Monad
import           Pirouette.Monad.Maybe
import           Pirouette.Monad.Logger
import qualified Pirouette.Term.Syntax as S
import           Pirouette.Term.Transformations
import           Pirouette.Term.DSL
import           Pirouette.PlutusIR.ToTerm
import qualified Pirouette.Term.Syntax.SystemF as R

import Data.List (groupBy, transpose, lookup)
import Control.Arrow (first)

import           Control.Monad
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Text.Prettyprint.Doc
import           Test.Hspec
import           Data.Maybe
import qualified Data.Set  as Set
import qualified Data.Map  as M
import qualified Data.Text as T

-- * Mocking a number of definitions for the PrtT monad

testingDefs :: [S.Name] -> [(S.Name, S.PrtDef PlutusIR)]
testingDefs extras =
  [("destMaybe", S.DDestructor "Maybe")
  ,("destEither", S.DDestructor "Either")
  ,("destSimple", S.DDestructor "Simple")
  ,("destExpr", S.DDestructor "Expr")
  ] ++ map stubsFor
  [ "F", "L", "E", "M", "R", "JJ", "JN", "IJ"
  , "IN", "J", "N", "JJJ", "JJN", "JNN", "NNN"
  , "AJ", "NR", "NJ", "S", "JL", "AN", "NN", "SJ", "NL"
  , "JR", "SN", "JNJ", "MJ", "MN", "NJJ", "NJN", "NNJ"
  , "def"
  ] ++ map withDummyFunc extras
 where
   stubsFor n = (n , S.DConstructor 0 n)

withDummyFunc :: S.Name -> (S.Name, S.PrtDef PlutusIR)
withDummyFunc s = (s, dummyFun)
  where
    dummyFun = S.DFunction S.Rec dummyTerm dummyType
    dummyTerm = R.termPure (R.F (S.FreeName "_"))
    dummyType = R.tyPure (R.F (S.TyFree "_"))

testState extras = PrtUnorderedDefs (M.fromList $ testingDefs extras) undefined

testOpts = PrtOpts DEBUG []

runPrtTest :: [S.Name] -> ReaderT (PrtUnorderedDefs PlutusIR) (PrtT Identity) a -> a
runPrtTest extras =
  either (error . show) id . fst . runIdentity . runPrtT testOpts . flip runReaderT (testState extras)

-- * Actual Tests

spec :: SpecWith ()
spec = return ()

-- The test terms grouped by their categories

tSwaps = [ ("tSwap1" , tSwap1)
         , ("tSwap2" , tSwap2)
         , ("tSwap3" , tSwap3)
         , ("tSwap4" , tSwap4)
         , ("tSwap5" , tSwap5)
         , ("tSwap6" , tSwap6)
         , ("tSwap7" , tSwap7)
         , ("tSwap8" , tSwap8)
         , ("tSwap9" , tSwap9)
         , ("tSwap10" , tSwap10)
         ]

tSwapFails = [("tSwapFails1" , tSwapFails1), ("tSwapFails2", tSwapFails2)]

tDNFs = [ ("tDNF1", tDNF1, tDNF1_res)
        , ("tDNF2", tDNF2, tDNF2_res)
        ]

-- Convenience matchers

matchMaybe :: TermM -> (TermM -> TermM) -> TermM -> TermM
matchMaybe v jst nth =
  caseof "Maybe" v
      [ "Just"    :->: jst
      , "Nothing" :->: nth
      ]

matchEither :: TermM -> (TermM -> TermM) -> (TermM -> TermM) -> TermM
matchEither v lft rgt =
  caseof "Either" v
      [ "Left"  :->: lft
      , "Right" :->: rgt
      ]

-- Swapping matchMaybe and matchEither:

tSwap1 = term $ lam2 $ \x y ->
  matchMaybe y
    (\jy -> matchEither x
             (\lx -> def "JL" .$$ [jy, lx])
             (\rx -> def "JR" .$$ [jy, rx]))
    (matchEither x
             (\lx -> def "NL" .$$ [lx])
             (\rx -> def "NR" .$$ [rx]))


tSwap2 = term $ lam2 $ \x y ->
  matchEither x
    (\lx -> matchMaybe y
             (\jy -> def "JL" .$$ [jy, lx])
                    (def "NL" .$$ [lx]))
    (\rx -> matchMaybe y
             (\jy -> def "JR" .$$ [jy, rx])
                    (def "NR" .$$ [rx]))

-- Swapping maybe and either with a function application on the match

tSwap3 = term $ lam3 $ \x y z ->
  matchEither x
    (\lx -> matchMaybe (def "F" .$ z)
             (\jy -> def "JL" .$$ [jy, lx])
                    (def "NL" .$$ [lx]))
    (\rx -> matchMaybe (def "F" .$ z)
             (\jy -> def "JR" .$$ [jy, rx])
                    (def "NR" .$$ [rx]))

-- Swapping matchMaybe and a more complex case on an expression tyoe:

tSwap4 = term $ lam2 $ \x y ->
  caseof "Expr" (def "E" .$ x)
      [ "Int" :->: (\i -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "IJ" .$$ [i, jy])
                                     (def "IN" .$ i))
      , "Add" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "AJ" .$$ [e1, e2, jy])
                                     (def "AN" .$$ [e1, e2]))
      , "Sub" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "SJ" .$$ [e1, e2, jy])
                                     (def "SN" .$$ [e1, e2]))
      , "Mul" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "MJ" .$$ [e1, e2, jy])
                                     (def "MN" .$$ [e1, e2]))
      , "If"  :->: (\c t e -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "IJ" .$$ [c, t, e, jy])
                                     (def "IN" .$$ [c,t,e]))
      ]

tSwap5 = term $ lam2 $ \x y ->
  matchMaybe (def "M" .$ y)
    (\jy -> caseof "Expr" (def "E" .$ x)
             [ "Int" :->: (\i     -> def "IJ" .$$ [i, jy])
             , "Add" :->: (\e1 e2 -> def "AJ" .$$ [e1, e2, jy])
             , "Sub" :->: (\e1 e2 -> def "SJ" .$$ [e1, e2, jy])
             , "Mul" :->: (\e1 e2 -> def "MJ" .$$ [e1, e2, jy])
             , "If"  :->: (\c t e -> def "IJ" .$$ [c, t, e, jy])
             ])
    (caseof "Expr" (def "E" .$ x)
             [ "Int" :->: (\i     -> def "IN" .$$ [i])
             , "Add" :->: (\e1 e2 -> def "AN" .$$ [e1, e2])
             , "Sub" :->: (\e1 e2 -> def "SN" .$$ [e1, e2])
             , "Mul" :->: (\e1 e2 -> def "MN" .$$ [e1, e2])
             , "If"  :->: (\c t e -> def "IN" .$$ [c, t, e])
             ])


-- And a slightly simpler case I used to debug a failure in tSwap4/5.
-- I might as well leave it here.

tSwap6 = term $ lam2 $ \x y ->
  caseof "Simple" (def "S" .$ x)
    [ "Simple" :->: (\a b c -> matchMaybe (def "M" .$ y)
                               (\jy -> def "SJ" .$$ [a, b, c, jy])
                               (def "SN" .$$ [a, b, c]))
    ]

tSwap7 = term $ lam2 $ \x y ->
  matchMaybe (def "M" .$ y)
    (\jy -> caseof "Simple" (def "S" .$ x)
             [ "Simple" :->: (\a b c -> def "SJ" .$$ [a, b, c, jy])
             ])
    (caseof "Simple" (def "S" .$ x)
             [ "Simple" :->: (\a b c -> def "SN" .$$ [a, b, c])
             ])

-- Now, let's make a large one with multiple constructors

tSwap8 = term $ lam3 $ \x y z ->
  matchMaybe x
    (\jx -> matchMaybe y
      (\jy -> matchMaybe z
        (\jz -> def "JJJ" .$$ [jx, jy, jz])
        (def "JJN" .$$ [jx, jy]))
      (matchMaybe z
        (\jz -> def "JNJ" .$$ [jx, jz])
        (def "JNN" .$ jx)))
    (matchMaybe y
      (\jy -> matchMaybe z
        (\jz -> def "NJJ" .$$ [jy, jz])
        (def "NJN" .$$ [jy]))
      (matchMaybe z
        (\jz -> def "NNJ" .$$ [jz])
        (def "NNN")))

-- This is the expected result of "swapNthDestr 1 tSwap8"
tSwap8_1 = term $ lam3 $ \x y z ->
  matchMaybe x
    (\jx -> matchMaybe z
      (\jz -> matchMaybe y
         (\jy -> def "JJJ" .$$ [jx, jy, jz])
         (def "JNJ" .$$ [jx, jz]))
      (matchMaybe y
         (\jy -> def "JJN" .$$ [jx, jy])
         (def "JNN" .$ jx)))
    (matchMaybe z
      (\jz -> matchMaybe y
        (\jy -> def "NJJ" .$$ [jy, jz])
        (def "NNJ" .$$ [jz]))
      (matchMaybe y
        (\jy -> def "NJN" .$$ [jy])
        (def "NNN")))

-- Swapping the topmost constructors now should yield:
tSwap8_2 = term $ lam3 $ \x y z ->
  matchMaybe z
    (\jz -> matchMaybe x
      (\jx -> matchMaybe y
         (\jy -> def "JJJ" .$$ [jx, jy, jz])
         (def "JNJ" .$$ [jx, jz]))
      (matchMaybe y
        (\jy -> def "NJJ" .$$ [jy, jz])
        (def "NNJ" .$$ [jz])))
    (matchMaybe x
      (\jx -> matchMaybe y
         (\jy -> def "JJN" .$$ [jx, jy])
         (def "JNN" .$ jx))
      (matchMaybe y
        (\jy -> def "NJN" .$$ [jy])
        (def "NNN")))

-- Ok, it seems we're having an off-by-one error with two maybes,
-- lets play with an easier option:

tSwap9 = term $ lam2 $ \y z ->
   matchMaybe y
     (\jy -> matchMaybe z
       (\jz -> def "JJ" .$$ [jy, jz])
       (def "JN" .$$ [jy]))
     (matchMaybe z
       (\jz -> def "NJ" .$$ [jz])
       (def "NN"))

tSwap10 = term $ lam2 $ \y z ->
   matchMaybe z
     (\jz -> matchMaybe y
       (\jy -> def "JJ" .$$ [jy, jz])
       (def "NJ" .$$ [jz]))
     (matchMaybe y
       (\jy -> def "JN" .$$ [jy])
       (def "NN"))

-- Found a problem on MultiSigStateMachine.flat when pulling the match on
-- the user input to the top level

tSwap11 = term $ lam3 $ \params ds i ->
  caseof "State" ds
    [ "State" :->: (\ds0 ds1 ->
      caseof "MSState" ds0
        [ "Collecting" :->: (\pmt pks thunk ->
          caseof "Input" i
            [ "Inc" :->: (\n -> def "IC" .$$ [ds0, ds1, pmt, pks, thunk, n])
            , "Dec" :->: (\n -> def "NC" .$$ [ds0, ds1, pmt, pks, thunk, n])
            ])
        , "Holding" :->: (\thunk ->
          caseof "Input" i
            [ "Inc" :->: (\n -> def "IH" .$$ [ds0, ds1, thunk, n])
            , "Dec" :->: (\n -> def "NH" .$$ [ds0, ds1, thunk, n])
            ])
        ] .$ def "Unit")
    ]


-- Some cases that should fail due to not matching on the same thing.

tSwapFails1 = term $ lam3 $ \x y z ->
  matchMaybe y
    (\jy -> matchEither x
             (\lx -> def "JL" .$$ [jy, lx])
             (\rx -> def "JR" .$$ [jy, rx]))
    (matchEither z
             (\lx -> def "NL" .$$ [lx])
             (\rx -> def "NR" .$$ [rx]))

tSwapFails2 = term $ lam3 $ \x y z ->
  matchMaybe y
    (\jy -> matchEither (def "F" .$ jy)
             (\lx -> def "JL" .$$ [jy, lx])
             (\rx -> def "JR" .$$ [jy, rx]))
    (matchEither (def "F" .$ z)
             (\lx -> def "NL" .$$ [lx])
             (\rx -> def "NR" .$$ [rx]))

-- Some terms NOT in DNF, which we want to convert to DNF with their respective expected result

tDNF1 = term $ lam2 $ \x y -> def "F" .$$
  [ matchEither x (\lx -> def "L" .$ lx) (\rx -> def "R" .$ rx)
  , matchMaybe y (\jy -> def "J" .$ jy) (def "NR")
  ]

tDNF1_res = term $ lam2 $ \x y ->
  matchEither x
    (\lx -> matchMaybe y (\jy -> def "F" .$$ [def "L" .$ lx, def "J" .$ jy])
                         (def "F" .$$ [def "L" .$ lx, def "NR"]))
    (\rx -> matchMaybe y (\jy -> def "F" .$$ [def "R" .$ rx, def "J" .$ jy])
                         (def "F" .$$ [def "R" .$ rx, def "NR"]))

tDNF2 = term $ lam2 $ \x y -> def "F" .$$
  [ y
  , caseof "Expr" (def "E" .$ x)
        [ "Int" :->: (\i -> matchMaybe (def "M" .$ y)
                                       (\jy -> def "IJ" .$$ [i, jy])
                                       (def "IN" .$ i))
        , "Add" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                       (\jy -> def "AJ" .$$ [e1, e2, jy])
                                       (def "AN" .$$ [e1, e2]))
        , "Sub" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                       (\jy -> def "SJ" .$$ [e1, e2, jy])
                                       (def "SN" .$$ [e1, e2]))
        , "Mul" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                       (\jy -> def "MJ" .$$ [e1, e2, jy])
                                       (def "MN" .$$ [e1, e2]))
        , "If"  :->: (\c t e -> matchMaybe (def "M" .$ y)
                                       (\jy -> def "IJ" .$$ [c, t, e, jy])
                                       (def "IN" .$$ [c,t,e]))
        ]
  ]

tDNF2_res = term $ lam2 $ \x y ->
  caseof "Expr" (def "E" .$ x)
      [ "Int" :->: (\i -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "F" .$$ [y, def "IJ" .$$ [i, jy]])
                                     (def "F" .$$ [y, def "IN" .$ i]))
      , "Add" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "F" .$$ [y, def "AJ" .$$ [e1, e2, jy]])
                                     (def "F" .$$ [y, def "AN" .$$ [e1, e2]]))
      , "Sub" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "F" .$$ [y, def "SJ" .$$ [e1, e2, jy]])
                                     (def "F" .$$ [y, def "SN" .$$ [e1, e2]]))
      , "Mul" :->: (\e1 e2 -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "F" .$$ [y, def "MJ" .$$ [e1, e2, jy]])
                                     (def "F" .$$ [y, def "MN" .$$ [e1, e2]]))
      , "If"  :->: (\c t e -> matchMaybe (def "M" .$ y)
                                     (\jy -> def "F" .$$ [y, def "IJ" .$$ [c, t, e, jy]])
                                     (def "F" .$$ [y, def "IN" .$$ [c,t,e]]))
      ]

tcfoldBool = term $ lam2 $ \x y ->
  tyApp (tyApp (func "fFoldableNil_cfoldMap") "Bool") "String" .$$
    [ func "CConsMonoid" .$$
        [ lam2 $ \b1 b2 ->
            caseof "Bool" b1
              [ "True"  :->: func "True"
              , "False" :->: b2
              ]
        , func "False"
        ]
    , lam1 $ \p -> func "Eq" .$$ [y, p]
    , x
    ]

tcfoldBoolSpec = term $ lam2 $ \ x y ->
  tyApp (tyApp (func "foldr0") "String") "Bool" .$$
    [ lam2_ann [("a","String"),("b","Bool")] $
      \a b -> caseofAnn "Bool_match" "Bool" "Bool" (func "Eq" .$$ [y, a])
        [ "True"  :->: func "True"
        , "False" :->: b
        ]
    , func "False"
    , x
    ]
