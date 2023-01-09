module UnionFind.Action where

data Action key value
  = Insert key value
  | Union key key
  deriving (Show)

isInsert :: Action key value -> Bool
isInsert (Insert _ _) = True
isInsert _ = False

isUnion :: Action key value -> Bool
isUnion (Union _ _) = True
isUnion _ = False
