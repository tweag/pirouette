{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UnionFind.Action where

import Test.QuickCheck ( Arbitrary, arbitrary )
import UnionFind.Internal (UnionFind)
import UnionFind.Monad ( insert, union, runWithUnionFind, WithUnionFind )
import qualified UnionFind.Dummy as DUF

data Action key value
  = Insert key value
  | Union key key
  deriving (Show)

instance (Arbitrary key, Arbitrary value) => Arbitrary (Action key value) where
  arbitrary =
    arbitrary >>= \case
      True -> Insert <$> arbitrary <*> arbitrary
      False -> Union <$> arbitrary <*> arbitrary

isInsert :: Action key value -> Bool
isInsert (Insert _ _) = True
isInsert _ = False

isUnion :: Action key value -> Bool
isUnion (Union _ _) = True
isUnion _ = False

applyActionM :: (Ord key, Num value) => Action key value -> WithUnionFind key value ()
applyActionM (Insert k v) = insert (+) k v
applyActionM (Union k1 k2) = union (+) k1 k2

applyActionToDummy :: (Ord key, Num value) => Action key value -> DUF.DummyUnionFind key value -> DUF.DummyUnionFind key value
applyActionToDummy (Insert k v) = DUF.insert (+) k v
applyActionToDummy (Union k1 k2) = DUF.union (+) k1 k2
