module UnionFindSpec (tests) where

import Data.Function ((&))
import Test.Tasty
import Test.Tasty.HUnit
import qualified UnionFind as UF
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

tests :: [TestTree]
tests =
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
