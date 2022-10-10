{-# LANGUAGE AllowAmbiguousTypes #-}

module Pirouette.SMT.Base where

import Data.Void
import Pirouette.Term.Syntax
import qualified PureSMT

-- | Captures the languages that can be translated to SMTLIB; namelly,
-- we need to be able to translate each individual base syntactical category.
--
-- This class is defined with @-XAllowAmbiguousTypes@ and therefore
-- should be used with @-XTypeApplications@ whenever necessary.
class (LanguageBuiltins lang) => LanguageSMT lang where
  translateBuiltinType :: BuiltinTypes lang -> PureSMT.SExpr
  translateBuiltinTerm :: BuiltinTerms lang -> [PureSMT.SExpr] -> Maybe PureSMT.SExpr
  translateConstant :: Constants lang -> PureSMT.SExpr
  isStuckBuiltin :: TermMeta lang meta -> Bool

-- | Captures arbitrary types that can be translated to SMTLIB.
class (Show t) => ToSMT t where
  translate :: t -> PureSMT.SExpr

instance ToSMT Void where
  translate = absurd

-- | Prefix Pirouette names with "pir" to avoid name clashes with SMT builtins
toSmtName :: Name -> String
toSmtName = ("pir_" <>) . show . pretty

instance ToSMT Name where
  translate = PureSMT.symbol . toSmtName

type WithDebugMessages = Bool
