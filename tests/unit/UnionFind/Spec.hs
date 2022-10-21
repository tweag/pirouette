{-# LANGUAGE LambdaCase #-}
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
import UnionFind.Action ( Action, isInsert, applyAction, applyActionToDummy )
import qualified UnionFind.Dummy as DUF

unionFindToNormalisedList :: (Ord key, Ord value) => UFI.UnionFind key value -> [([key], Maybe value)]
unionFindToNormalisedList = sort . map (first (sort . NE.toList)) . snd . UFI.toList

dummyUnionFindToNormalisedList :: (Ord key, Ord value) => DUF.DummyUnionFind key value -> [([key], Maybe value)]
dummyUnionFindToNormalisedList = sort . map (first sort)

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
              -- Run the same actions in different orders
              result1 = snd $ runWithUnionFind $ mapM applyAction actions
              result2 = snd $ runWithUnionFind $ mapM applyAction insertsFirst
              result3 = snd $ runWithUnionFind $ mapM applyAction unionsFirst
              -- Normalise outputs
              sorted1 = unionFindToNormalisedList result1
              sorted2 = unionFindToNormalisedList result2
              sorted3 = unionFindToNormalisedList result3
           in sorted1 QC.=== sorted2
                QC..&&. sorted1 QC.=== sorted3
      ,
      testCase "#1" $
        let uf1 = UFI.union (+) 10 2 $ UFI.union (+) 11 10 $ UFI.insert (+) 2 0 UF.empty
            uf2 = UFI.insert (+) 2 0 $ UFI.union (+) 11 10 $ UFI.union (+) 10 2 UF.empty
            nuf1 = unionFindToNormalisedList uf1
            nuf2 = unionFindToNormalisedList uf2
         in nuf1 @?= nuf2
      ]
  ,

    testGroup "behaves like dummy" [
      testProperty "QuickCheck" $
        \(actions :: [Action Int Int]) ->
          let result = snd $ runWithUnionFind $ mapM applyAction actions
              sorted = unionFindToNormalisedList result
              result' = foldl (flip applyActionToDummy) [] actions
              sorted' = dummyUnionFindToNormalisedList result'
           in sorted QC.=== sorted'
      ,
      testCase "#1" $
        let uf = UFI.union (+) 8 8 UF.empty
            duf = DUF.union (+) 8 8 []
            nuf = unionFindToNormalisedList uf
            nduf = dummyUnionFindToNormalisedList duf
         in nuf @?= nduf
      ]
  ]
