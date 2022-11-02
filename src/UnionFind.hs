module UnionFind
  ( UnionFind,
    empty,
    lookup,
    unionWith,
    trivialUnion,
    union,
    insertWith,
    trivialInsert,
    insert,
    applyActionWith,
    applyAction,
    toLists,
    toList,
  )
where

import UnionFind.Internal
import UnionFind.Monadic
import Prelude ()
