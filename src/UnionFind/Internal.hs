-- | This module implements a persistent union-find data structure. This
-- structure reprensents a map from equivalence classes of keys to values. The
-- equivalence relation is irrelevant. The structure primarily provides two
-- operations:
--
-- - @union@ takes two keys and merges their equivalence classes, returning a
--   new structure. Because both keys might be associated to a value, this
--   operation must also be told how to reconcile both values into one.
--
-- - @find@ takes a key and returns the value associated to the key's
--   equivalence class. In order for the structure to remain efficient, @find@
--   also optimises it for future calls and therefore returns a new structure.
module UnionFind.Internal where

import Data.Default (Default, def)
import Data.Map (Map)
import qualified Data.Map as Map

data UnionFindCell key value
  = ChildOf key
  | Ancestor Int (Maybe value)

-- | A persistent union-find data structure.
--
-- Invariants:
--
--   (i) There are no cycles.
--   (ii) Keys under @ChildOf@ are present in the map.
--
-- The points (i) and (ii) imply that, if a key is present in the map, then
-- there is a path made of @ChildOf@ constructors from that key to an @Ancestor@
-- constructor.
newtype UnionFind key value = UnionFind
  { getMap :: Map key (UnionFindCell key value)
  }

instance Default (UnionFind key value) where
  def = empty

-- | The empty union-find that does not know of any equivalences or values.
empty :: UnionFind key value
empty = UnionFind Map.empty
