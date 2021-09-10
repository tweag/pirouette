module Pirouette.Specializer
  ( module Pirouette.Specializer
  , module Pirouette.Specializer.TypeDecl
  ) where

import Pirouette.Specializer.TypeDecl
import Pirouette.Specializer.Basics

allSpz :: String -> Maybe TypeSpecializer
allSpz "Bool"   = Just boolSpz
allSpz "List"   = Just listSpz
allSpz "Unit"   = Just unitSpz
allSpz "Tuple2" = Just tuple2Spz
allSpz _        = Nothing