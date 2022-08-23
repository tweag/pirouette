{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Term.IL where

import Data.Data
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import qualified Language.Pirouette.QuasiQuoter.Syntax as QQ
import Pirouette.SMT
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF

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
liftTypeIL (TyApp var args) = TyApp var' (liftTypeIL <$> args)
  where
    var' :: TyVarMeta (IL lang) Void
    var' = case var of
                Bound a n -> Bound a n
                Free (TySig n) -> Free (TySig n)
                Free (TyBuiltin b) -> Free (TyBuiltin b)
                Meta m -> Meta m
liftTypeIL (TyFun t1 t2) = TyFun (liftTypeIL t1) (liftTypeIL t2)
liftTypeIL (TyLam a k ty) = TyLam a k $ liftTypeIL ty
liftTypeIL (TyAll a k ty) = TyAll a k $ liftTypeIL ty

instance LanguageBuiltinTypes lang => LanguageBuiltinTypes (IL lang) where
  typeOfBottom = liftTypeIL typeOfBottom
  typeOfConstant = liftTypeIL . typeOfConstant
  typeOfBuiltin (Left _triple) = typeOfBottom -- it's not, really
  typeOfBuiltin (Right base) = liftTypeIL $ typeOfBuiltin base

instance LanguageSMT lang => LanguageSMT (IL lang) where
  translateBuiltinType = translateBuiltinType @lang
  translateConstant = translateConstant @lang

  -- but how to parallelize evaluation if we were to translate this?
  -- what'd be the benefit of having this as opposed to just having a (nested) if-then-else?
  translateBuiltinTerm (Left triple) = undefined
  translateBuiltinTerm (Right base) = translateBuiltinTerm @lang base

  isStuckBuiltin b = _

--instance (Lift (Term lang), QQ.LanguageParser lang) => QQ.LanguageParser (IL lang) where
