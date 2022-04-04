{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Transformations.MonomorphizationSpec (tests) where

import Control.Monad.Reader
import Control.Monad.Writer
import Data.List (sort)
import qualified Data.Map as M
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Monomorphization
import Pirouette.Transformations.Utils
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

sampleProgram :: Program Ex
sampleProgram =
  [prog|
data Maybe (a : Type)
  = Nothing : Maybe a
  | Just : a -> Maybe a

data Monoid (a : Type)
  = Mon : a -> (a -> a -> a) -> Monoid a

data List (a : Type)
  = Cons : a -> List a -> List a
  | Nil : List a

fun fold : all a : Type . Monoid a -> List a -> a
      = /\ a : Type . \(m : Monoid a) (xs : List a)
      . match_Monoid @a m @a
          (\(zero : a) (mplus : a -> a -> a)
            . match_List @a xs @a
                (\(x : a) (xs2 : List a) . mplus a (fold m xs2))
                zero
          )

fun intMonoid : Monoid Integer
     = Mon @Integer 0 (\(x : Integer) (y : Integer) . x + y)

fun myList : List Integer
      = Cons @Integer 3 (Cons @Integer 12 (Nil @Integer))

fun main : Integer = fold @Integer intMonoid myList
|]

sampleUDefs :: PrtUnorderedDefs Ex
sampleUDefs = uncurry PrtUnorderedDefs sampleProgram

withSampleUDefs ::
  (forall m. PirouetteReadDefs Ex m => m Assertion) ->
  Assertion
withSampleUDefs m =
  case mockPrt (runReaderT m sampleUDefs) of
    Left err -> assertFailure err
    Right t -> t

tests :: [TestTree]
tests =
  [ -- We expect that 'Monoid' is a higher-order definition and is picked by findPolyHOFDefs
    testCase "findPolyHOFDefs picks 'Monoid'" $
      assertBool "not there" $ "Monoid" `M.member` findPolyHOFDefs (prtUODecls sampleUDefs),
    -- In order to get the transitive closure of all the definitions that use ho-defs,
    -- we rely on 'hofsClosure':
    testCase "hofsClosure picks the expected defs" $
      let ds = prtUODecls sampleUDefs
       in M.keys (hofsClosure ds (findPolyHOFDefs ds)) @?= ["Mon", "Monoid", "fold", "match_Monoid"],
    -- Now we make sure that the function specialization requests are working as we expect:
    testGroup
      "specFunApp"
      [ testCase "specFunApp (id @Bool True) == (id@Bool True, [SpecRequest ...])" $
          let idBool x = SystF.Free (TermSig "id@TyBool") `SystF.App` [SystF.TermArg x]
           in runWriter (specFunApp (M.singleton "id" idDef) [term| id @Bool True |])
                @?= (idBool [term| True |], [SpecRequest idDef [[ty| Bool |]]]),
        -- TODO: Test fails because we're only monomorphizing the first type variable
        expectFail $
        testCase "specFunApp (const @Integer @Bool 42 False) == (const@Integer@Bool 42 False, [SpecRequest ...])" $
          let constIntBool x y =
                SystF.Free (TermSig "const@TyInteger@TyBool")
                  `SystF.App` [SystF.TermArg x, SystF.TermArg y]
           in runWriter (specFunApp (M.singleton "const" constDef) [term| const @Integer @Bool 42 True |])
                @?= (constIntBool [term| 42 |] [term| True |], [SpecRequest constDef [[ty| Integer |], [ty| Bool |]]])
      ]
  ]

constDef :: HofDef Ex
constDef = HofDef "const" $ HDBFun $ FunDef Rec funterm funtype
  where
    funtype = [ty| all (a : Type) (b : Type) . a -> b -> a |]
    funterm = [term| /\ (a : Type) (b : Type) . \ (x : a) (y : b) . x |]

idDef :: HofDef Ex
idDef = HofDef "id" $ HDBFun $ FunDef Rec funterm funtype
  where
    funtype = [ty| all a : Type . a -> a |]
    funterm = [term| /\ a : Type . \ x : a . x |]
