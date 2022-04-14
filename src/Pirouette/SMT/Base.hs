{-# LANGUAGE AllowAmbiguousTypes #-}

module Pirouette.SMT.Base where

import Control.Monad.IO.Class
import Data.Void
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import Pirouette.Term.Syntax


-- | Captures the languages that can be translated to SMTLIB; namelly,
-- we need to be able to translate each individual base syntactical category.
--
-- This class is defined with @-XAllowAmbiguousTypes@ and therefore
-- should be used with @-XTypeApplications@ whenever necessary.
class (LanguageBuiltins lang) => LanguageSMT lang where
  translateBuiltinType :: BuiltinTypes lang -> SimpleSMT.SExpr
  translateBuiltinTerm :: BuiltinTerms lang -> [SimpleSMT.SExpr] -> Maybe SimpleSMT.SExpr
  translateConstant :: Constants lang -> SimpleSMT.SExpr

-- | Captures arbitrary types that can be translated to SMTLIB.
class (Show t) => ToSMT t where
  translate :: t -> SimpleSMT.SExpr

instance ToSMT Void where
  translate = absurd

-- | Prefix Pirouette names with "pir" to avoid name clashes with SMT builtins
toSmtName :: Name -> String
toSmtName = ("pir_" <>) . show . pretty

instance ToSMT Name where
  translate = SimpleSMT.symbol . toSmtName

type WithDebugMessages = Bool

-- | Prepare a CVC4 solver with all supported theories, which is necessary
-- to handle datatypes. The boolean parameter controls debug messages.
-- The "fmf-fun" options is much better at finding sat by constructing finite model of recursive functions,
-- whereas "full-saturate-quant" makes a much better use of the universally quantified hints to find unsat.
cvc4_ALL_SUPPORTED :: (MonadIO m) => WithDebugMessages -> m SimpleSMT.Solver
cvc4_ALL_SUPPORTED dbg = do
  -- This generates a "Solver" which logs every interaction it has.
  ml <- if dbg then Just <$> liftIO (SimpleSMT.newLogger 0) else return Nothing
  s <- liftIO $ SimpleSMT.newSolver "cvc4" ["--lang=smt2", "--incremental", "--fmf-fun"] ml
  liftIO $ SimpleSMT.setLogic s "ALL"
  return s
