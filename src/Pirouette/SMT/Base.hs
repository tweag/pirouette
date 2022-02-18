{-# LANGUAGE AllowAmbiguousTypes #-}
module Pirouette.SMT.Base where

import Control.Monad.IO.Class
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import Pirouette.Term.Syntax
import Data.Void

-- | Captures the languages that can be translated to SMTLIB; namelly,
-- we need to be able to translate each individual base syntactical category.
--
-- This class is defined with @-XAllowAmbiguousTypes@ and therefore
-- should be used with @-XTypeApplications@ whenever necessary.
class (LanguageDef lang) => LanguageSMT lang where
  translateBuiltinType :: BuiltinTypes lang -> SimpleSMT.SExpr
  translateBuiltinTerm :: BuiltinTerms lang -> SimpleSMT.SExpr
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
cvc4_ALL_SUPPORTED :: MonadIO m => WithDebugMessages -> m SimpleSMT.Solver
cvc4_ALL_SUPPORTED dbg = do
  -- This generates a "Solver" which logs every interaction it has.
  -- To suppress this logging, replace the 2 next lines by
  -- s <- liiftIO $ SimpleSMT.newSolver "cvc4" ["--lang=smt2"] Nothing
  ml <- if dbg then Just <$> liftIO (SimpleSMT.newLogger 0) else return Nothing
  s <- liftIO $ SimpleSMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] ml
  liftIO $ SimpleSMT.setLogic s "ALL_SUPPORTED"
  return s
