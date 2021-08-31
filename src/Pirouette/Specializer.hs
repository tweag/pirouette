module Pirouette.Specializer
  ( module Pirouette.Specializer
  , module Pirouette.Specializer.TypeDecl
  ) where

import Pirouette.Specializer.TypeDecl
import Pirouette.Specializer.Basics

allSpz :: String -> TypeSpecializer
allSpz "Bool"   = boolSpz
allSpz "List"   = listSpz
allSpz "Unit"   = unitSpz
allSpz "Tuple2" = tuple2Spz
allSpz "Maybe"  = maybeSpz