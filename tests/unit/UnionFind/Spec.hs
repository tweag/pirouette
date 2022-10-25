{-# LANGUAGE ScopedTypeVariables #-}

module UnionFind.Spec (tests) where

import Data.Bifunctor (first)
import Data.Function ((&))
import Data.List (partition, sort)
import qualified Data.List.NonEmpty as NE
import qualified Test.QuickCheck as QC
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck (testProperty)
import qualified UnionFind as UF
import qualified UnionFind.Internal as UFI
import UnionFind.Monad
import UnionFind.Action ( Action(..), isInsert, applyActionToDummy, applyActionM )
import qualified UnionFind.Dummy as DUF

unionFindToNormalisedList :: (Ord key, Ord value) => UFI.UnionFind key value -> [([key], Maybe value)]
unionFindToNormalisedList = sort . map (first (sort . NE.toList)) . snd . UFI.toList

dummyUnionFindToNormalisedList :: (Ord key, Ord value) => DUF.DummyUnionFind key value -> [([key], Maybe value)]
dummyUnionFindToNormalisedList = sort . map (first sort)

mkNormalWithActions :: (Ord key, Ord value, Num value) => [Action key value] -> [([key], Maybe value)]
mkNormalWithActions = unionFindToNormalisedList . snd . runWithUnionFind . mapM applyActionM

mkDummyNormalWithActions :: (Ord key, Ord value, Num value) => [Action key value] -> [([key], Maybe value)]
mkDummyNormalWithActions = dummyUnionFindToNormalisedList . foldl (flip applyActionToDummy) []

tests :: [TestTree]
tests = [
  testGroup "manual Runs" [
      testCase "#1" $
        let nuf =
              unionFindToNormalisedList $
              snd $
                runWithUnionFind $ do
                  trivialInsert 2 2
                  trivialInsert 3 3
                  trivialInsert 4 4
                  trivialInsert 5 5
                  union (+) 3 4
                  trivialUnion 5 6
                  trivialUnion 7 8
         in nuf @?= [ ([2], Just 2), ([3, 4], Just 7), ([5, 6], Just 5), ([7, 8], Nothing) ]
      ]
  ,

  testGroup "lookup . insert == id" [
    testProperty "QuickCheck" $
      \(k :: Int) (v :: Int) -> snd (UFI.lookup k $ UFI.trivialInsert k v UFI.empty) == Just v
    ]
  ,

    testGroup "lookup . insert . insert == (<>)" [
      testProperty "QuickCheck" $
        \(k :: Int) (v1 :: Int) v2 ->
          snd (UFI.lookup k $ UFI.insert (+) k v2 $ UFI.insert (+) k v1 UFI.empty)
          == Just (v1 + v2)
      ]
  ,

    testGroup "actions are commutative" [
      testProperty "QuickCheck" $
        \(actions :: [Action Int Int]) ->
          let (inserts, unions) = partition isInsert actions
              insertsFirst = inserts ++ unions
              unionsFirst = unions ++ inserts
              -- Run the same actions in different orders, normalise.
              result1 = mkNormalWithActions actions
              result2 = mkNormalWithActions insertsFirst
              result3 = mkNormalWithActions unionsFirst
           in result1 QC.=== result2
                QC..&&. result1 QC.=== result3
      ,
      testCase "#1" $
        let uf1 = mkNormalWithActions [Insert 2 0, Union 11 10, Union 10 2]
            uf2 = mkNormalWithActions [Union 10 2, Union 11 10, Insert 2 0]
         in uf1 @?= uf2
      ]
  ,

    testGroup "behaves like dummy" [
      testProperty "QuickCheck" $
        \(actions :: [Action Int Int]) ->
          let result = mkNormalWithActions actions
              result' = mkDummyNormalWithActions actions
           in result QC.=== result'
      ,
      testCase "#1" $
        let uf = mkNormalWithActions [Union 8 8]
            duf = mkDummyNormalWithActions [Union 8 8]
         in uf @?= duf
      ,
      testCase "#2" $
      let actions = [Insert 7 4, Union 13 8, Union 7 13]
       in mkNormalWithActions actions @?= mkDummyNormalWithActions actions
      ]
  ]
