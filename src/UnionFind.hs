module UnionFind
  ( UnionFind,
    empty,
    lookup,
    insertWith,
    trivialInsert,
    unionWith,
    trivialUnion,
    toList,
    toLists,
  )
where

import UnionFind.Internal
    ( toLists,
      lookup,
      toList,
      empty,
      UnionFind,
      unionWith,
      trivialUnion,
      insertWith,
      trivialInsert )
import Prelude ()
