{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Pirouette.Term.Builtins where

import Data.Data (Data)
import Data.Typeable (Typeable)
import Pirouette.Term.Syntax.Pretty.Class
import Language.Haskell.TH.Syntax (Lift)

type EqOrdShowDataTypeableLift a = (Eq a, Ord a, Show a, Data a, Typeable a, Lift a)

type LanguageConstrs builtins =
  ( EqOrdShowDataTypeableLift (BuiltinTypes builtins),
    EqOrdShowDataTypeableLift (BuiltinTerms builtins),
    EqOrdShowDataTypeableLift (Constants builtins)
  )

type PrettyLang builtins =
  ( Pretty (BuiltinTypes builtins),
    Pretty (BuiltinTerms builtins),
    Pretty (Constants builtins)
  )

-- The builtins of a language.
-- We distinguish the `Constants` which are the constructors of objects of the `BuiltinTypes`
-- and the other builtin objects (essentially functions manipulating those obects).
class (Data builtins, Typeable builtins, LanguageConstrs builtins) => LanguageBuiltins builtins where
  type BuiltinTypes builtins :: *
  type BuiltinTerms builtins :: *
  type Constants builtins :: *
