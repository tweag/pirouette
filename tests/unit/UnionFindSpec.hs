{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UnionFindSpec (tests) where

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

uf1 :: UF.UnionFind Int Int
uf1 =
  snd $
    runWithUnionFind $ do
      trivialInsert 2 2
      trivialInsert 3 3
      trivialInsert 4 4
      trivialInsert 5 5
      union (+) 3 4
      trivialUnion 5 6
      trivialUnion 7 8

basicSmoke :: TestTree
basicSmoke =
  testGroup
    "Basic smoke tests"
    [ testCase "Lookup 1 in uf1" $ snd (UF.lookup 1 uf1) @?= Nothing,
      testCase "Lookup 2 in uf1" $ snd (UF.lookup 2 uf1) @?= Just 2,
      testCase "Lookup 3 in uf1" $ snd (UF.lookup 3 uf1) @?= Just 7,
      testCase "Lookup 4 in uf1" $ snd (UF.lookup 4 uf1) @?= Just 7,
      testCase "Lookup 5 in uf1" $ snd (UF.lookup 5 uf1) @?= Just 5,
      testCase "Lookup 6 in uf1" $ snd (UF.lookup 6 uf1) @?= Just 5,
      testCase "Lookup 7 in uf1" $ snd (UF.lookup 7 uf1) @?= Nothing,
      testCase "Lookup 8 in uf1" $ snd (UF.lookup 8 uf1) @?= Nothing,
      testCase "Lookup 9 in uf1" $ snd (UF.lookup 9 uf1) @?= Nothing
    ]

data Action key value
  = Insert key value
  | Union key key
  deriving (Show)

instance (QC.Arbitrary key, QC.Arbitrary value) => QC.Arbitrary (Action key value) where
  arbitrary =
    QC.arbitrary >>= \case
      True -> Insert <$> QC.arbitrary <*> QC.arbitrary
      False -> Union <$> QC.arbitrary <*> QC.arbitrary

isInsert :: Action key value -> Bool
isInsert (Insert _ _) = True
isInsert _ = False

applyAction :: (Ord key, Num value) => Action key value -> WithUnionFind key value ()
applyAction (Insert k v) = insert (+) k v
applyAction (Union k1 k2) = union (+) k1 k2

props :: TestTree
props =
  testGroup
    "Some properties"
    [ testProperty "trivially inserting and finding the value succeeds" $
        \(k :: Int) (v :: Int) -> snd (UFI.lookup k $ UFI.trivialInsert k v UFI.empty) == Just v,
      testProperty "inserting combines" $
        \(k :: Int) (v1 :: Int) v2 -> snd (UFI.lookup k $ UFI.insert (+) k v2 $ UFI.insert (+) k v1 UFI.empty) == Just (v1 + v2),
      testProperty "reordering actions works" $
        \(actions :: [Action Int Int]) ->
          let (inserts, unions) = partition isInsert actions
              insertsFirst = inserts ++ unions
              unionsFirst = unions ++ inserts
              -- Run the same actions in different orders
              result1 = snd $ runWithUnionFind $ mapM applyAction actions
              result2 = snd $ runWithUnionFind $ mapM applyAction insertsFirst
              result3 = snd $ runWithUnionFind $ mapM applyAction unionsFirst
              -- Normalise outputs
              sorted1 = sort $ map (first (sort . NE.toList)) $ snd $ UFI.toList result1
              sorted2 = sort $ map (first (sort . NE.toList)) $ snd $ UFI.toList result2
              sorted3 = sort $ map (first (sort . NE.toList)) $ snd $ UFI.toList result3
           in sorted1 QC.=== sorted2
                QC..&&. sorted1 QC.=== sorted3
    ]

tests :: [TestTree]
tests =
  [ basicSmoke,
    props
  ]
