{-# LANGUAGE ScopedTypeVariables #-}

module UnionFindSpec (tests) where

import Data.Function ((&))
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

props :: TestTree
props =
  testGroup
    "Some properties"
    [ testProperty "trivially inserting and finding the value succeeds" $
        \(k :: Int) (v :: Int) -> snd (UFI.lookup k $ UFI.trivialInsert k v UFI.empty) == Just v,
      testProperty "inserting combines" $
        \(k :: Int) (v1 :: Int) v2 -> snd (UFI.lookup k $ UFI.insert (+) k v2 $ UFI.insert (+) k v1 UFI.empty) == Just (v1 + v2)
    ]

tests :: [TestTree]
tests =
  [ basicSmoke,
    props
  ]
