{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Term.IL where

import Data.Data
import Language.Haskell.TH.Syntax (Lift)
import qualified Language.Pirouette.QuasiQuoter.Syntax as QQ
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF
import Data.Void

data ILTriple lang = ILTriple
  { iltBody :: Term lang
  , iltAssume :: Term lang
  , iltProve :: Term lang
  } deriving (Eq, Ord, Show, Data, Typeable)

deriving instance Lift (Term lang) => Lift (ILTriple lang)

type ILTerm lang = Either (ILTriple lang) (BuiltinTerms lang)

data IL lang deriving (Data)


instance LanguageBuiltins lang => LanguageBuiltins (IL lang) where
  type BuiltinTypes (IL lang) = BuiltinTypes lang
  type Constants (IL lang) = Constants lang
  type BuiltinTerms (IL lang) = ILTerm lang

liftTypeIL :: forall lang. Type lang -> Type (IL lang)
liftTypeIL = undefined

instance LanguageBuiltinTypes lang => LanguageBuiltinTypes (IL lang) where
  typeOfBottom = liftTypeIL typeOfBottom
  typeOfConstant = liftTypeIL . typeOfConstant
  typeOfBuiltin (Left triple) = typeOfBottom -- it's not, really
  typeOfBuiltin (Right base) = liftTypeIL $ typeOfBuiltin base

instance QQ.LanguageParser lang => QQ.LanguageParser (IL lang) where
