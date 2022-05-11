-- | Examples of weighted search, taken from
-- https://hackage.haskell.org/package/weighted-search-0.1.0.1/docs/Control-Monad-WeightedSearch.html
module ListT.Weighted.Examples where

import Data.Functor.Identity
import ListT.Weighted

-- All naturals, weighted by the size of the number
naturals :: Weighted Integer Integer
naturals = go 0
  where
    go n = pure n <|> weight 1 (go $! n + 1)

-- All finite lists, weighted by the length of the list
finiteLists :: Weighted Integer a -> Weighted Integer [a]
finiteLists w = pure [] <|> weight 1 ((:) <$> w <*> finiteLists w)

-- A list of all finite lists of naturals
finiteListsOfNaturals :: [[Integer]]
finiteListsOfNaturals = runIdentity $ ListT.Weighted.toList (finiteLists naturals)

-- [ [], [0], [0,0], [1], [0,0,0], [0,1], [1,0], [2], [0,0,0,0], [0,0,1], ... ]
