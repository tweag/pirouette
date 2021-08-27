{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

module Pirouette.TLA.Specializer where

import GHC.Generics
import Data.Aeson (FromJSON, decodeStrict)

newtype Cons a = Cons {
  cons :: a
} deriving (Generic, Show, Functor, Foldable, Traversable)

instance FromJSON a => FromJSON (Cons a)

data DatatypeEncoding a = DatatypeEncoding {
  spzSet :: a,
  spzConstructors :: [Cons a],
  spzDestructor :: a
} deriving (Generic, Show)

instance FromJSON a => FromJSON (DatatypeEncoding a)

instance Functor DatatypeEncoding where
  fmap f (DatatypeEncoding set c dest) =
    DatatypeEncoding (f set) (map (fmap f) c) (f dest)

instance Foldable DatatypeEncoding where
  foldMap f (DatatypeEncoding set c dest) =
    f set `mappend` foldMap (f . cons) c `mappend` f dest

instance Traversable DatatypeEncoding where
  traverse f (DatatypeEncoding set c dest) = do
    DatatypeEncoding <$> f set <*> traverse (traverse f) c <*> f dest