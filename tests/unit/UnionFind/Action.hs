{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UnionFind.Action where

import Test.QuickCheck ( Arbitrary, arbitrary )
import UnionFind.Monad ( insert, union, WithUnionFind )

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

applyAction :: (Ord key, Num value) => Action key value -> WithUnionFind key value ()
applyAction (Insert k v) = insert (+) k v
applyAction (Union k1 k2) = union (+) k1 k2
