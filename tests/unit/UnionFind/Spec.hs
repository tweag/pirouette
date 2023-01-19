{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UnionFind.Spec (tests) where

import Data.Bifunctor (first)
import Data.Function ((&))
import Data.List (partition, sort)
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Sum (..))
import Test.QuickCheck (Arbitrary, arbitrary)
import qualified Test.QuickCheck as QC
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck (testProperty)
import qualified UnionFind as UF
import UnionFind.Action (Action (..), isInsert)
import qualified UnionFind.Dummy as DUF

instance (Arbitrary key, Arbitrary value) => Arbitrary (Action key value) where
  arbitrary =
    arbitrary >>= \case
      True -> Insert <$> arbitrary <*> arbitrary
      False -> Union <$> arbitrary <*> arbitrary

unionFindToNormalisedList :: (Ord key, Ord value) => UF.UnionFind key value -> [([key], Maybe value)]
unionFindToNormalisedList = sort . map (first (sort . NE.toList)) . (\uf -> fst $ UF.runWithUnionFind uf UF.toList)

dummyUnionFindToNormalisedList :: (Ord key, Ord value) => DUF.DummyUnionFind key value -> [([key], Maybe value)]
dummyUnionFindToNormalisedList = sort . map (first sort)

mkNormalWithActions ::
  (Ord key, Ord value, Num value) =>
  [Action key (Sum value)] ->
  [([key], Maybe (Sum value))]
mkNormalWithActions = unionFindToNormalisedList . snd . UF.runWithEmptyUnionFind . mapM UF.applyAction

mkDummyNormalWithActions ::
  (Ord key, Ord value, Num value) =>
  [Action key (Sum value)] ->
  [([key], Maybe (Sum value))]
mkDummyNormalWithActions = dummyUnionFindToNormalisedList . foldl (flip DUF.applyAction) []

tests :: [TestTree]
tests =
  [ testGroup
      "manual Runs"
      [ testCase "#1" $
          let nuf =
                unionFindToNormalisedList $
                  snd $
                    UF.runWithEmptyUnionFind $ do
                      UF.trivialInsert 2 2
                      UF.trivialInsert 3 3
                      UF.trivialInsert 4 4
                      UF.trivialInsert 5 5
                      UF.unionWith (+) 3 4
                      UF.trivialUnion 5 6
                      UF.trivialUnion 7 8
           in nuf @?= [([2], Just 2), ([3, 4], Just 7), ([5, 6], Just 5), ([7, 8], Nothing)]
      ],
    testGroup
      "lookup . insert == id"
      [ testProperty "QuickCheck" $
          \(k :: Int) (v :: Int) ->
            fst (UF.runWithEmptyUnionFind $ UF.trivialInsert k v >> UF.lookup k)
              == Just v
      ],
    testGroup
      "lookup . insert . insert == (<>)"
      [ testProperty "QuickCheck" $
          \(k :: Int) (v1 :: (Sum Int)) v2 ->
            fst (UF.runWithEmptyUnionFind $ UF.insert k v1 >> UF.insert k v2 >> UF.lookup k)
              == Just (v1 + v2)
      ],
    testGroup
      "actions are commutative"
      [ testProperty "QuickCheck" $
          \(actions :: [Action Int (Sum Int)]) ->
            let (inserts, unions) = partition isInsert actions
                insertsFirst = inserts ++ unions
                unionsFirst = unions ++ inserts
                -- Run the same actions in different orders, normalise.
                result1 = mkNormalWithActions actions
                result2 = mkNormalWithActions insertsFirst
                result3 = mkNormalWithActions unionsFirst
             in result1 QC.=== result2
                  QC..&&. result1 QC.=== result3,
        testCase "#1" $
          let uf1 = mkNormalWithActions [Insert 2 0, Union 11 10, Union 10 2]
              uf2 = mkNormalWithActions [Union 10 2, Union 11 10, Insert 2 0]
           in uf1 @?= uf2
      ],
    testGroup
      "behaves like dummy"
      [ testProperty "QuickCheck" $
          \(actions :: [Action Int (Sum Int)]) ->
            let result = mkNormalWithActions actions
                result' = mkDummyNormalWithActions actions
             in result QC.=== result',
        testCase "#1" $
          let uf = mkNormalWithActions [Union 8 8]
              duf = mkDummyNormalWithActions [Union 8 8]
           in uf @?= duf,
        testCase "#2" $
          let actions = [Insert 7 4, Union 13 8, Union 7 13]
           in mkNormalWithActions actions @?= mkDummyNormalWithActions actions
      ]
  ]
