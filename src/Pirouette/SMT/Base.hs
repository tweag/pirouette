{-# LANGUAGE AllowAmbiguousTypes #-}

module Pirouette.SMT.Base where

import Control.Monad.IO.Class
import Data.Void
import qualified PureSMT
import Pirouette.Term.Syntax

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
  -- | Definitions required for built-in types
  builtinTypeDefinitions :: 
    [(Name, TypeDef lang)]    -- ^ types which are already defined
    -> [(Name, TypeDef lang)] -- ^ additional definitions supporting those
  builtinTypeDefinitions _ = []

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

-- | Prepare a CVC4 solver with all supported theories, which is necessary
-- to handle datatypes. The boolean parameter controls debug messages.
-- The "fmf-fun" options is much better at finding sat by constructing finite model of recursive functions,
-- whereas "full-saturate-quant" makes a much better use of the universally quantified hints to find unsat.
cvc4_ALL_SUPPORTED :: (MonadIO m) => WithDebugMessages -> m PureSMT.Solver
cvc4_ALL_SUPPORTED dbg = do
  s <- liftIO $ PureSMT.launchSolverWithFinalizer "cvc4 --lang=smt2 --incremental --fmf-fun" dbg
  liftIO $ PureSMT.setLogic s "ALL"
  return s
