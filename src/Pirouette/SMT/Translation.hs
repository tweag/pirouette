{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Translation of Pirouette syntactical categories into
-- smtlib through our copy of the SimpleSMT library.
module Pirouette.SMT.Translation where

import Control.Monad.IO.Class
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Debug.Trace
import Pirouette.Monad
import Pirouette.SMT.Common
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF

-- | Prefix Pirouette names with "pir" to avoid name clashes with SMT builtins
toSmtName :: Name -> String
toSmtName = ("pir_" <>) . show . pretty

translateTypeBase :: forall lang . (LanguageSMT lang) => TypeBase lang Name -> SmtLib.SExpr
translateTypeBase (TyBuiltin pirType) = translateBuiltinType @lang pirType
translateTypeBase (TyFree name) = SmtLib.symbol (toSmtName name)

translateType :: (LanguageSMT lang, ToSMT meta) => PrtTypeMeta lang meta -> SmtLib.SExpr
translateType (TyApp (F ty) args) = SmtLib.app (translateTypeBase ty) (map translateType args)
translateType (TyApp (B (Ann ann) index) args) =
  SmtLib.app (SmtLib.symbol (toSmtName ann)) (map translateType args)
translateType x = error $ "Translate type to smtlib: cannot handle " <> show x

-- TODO: The translation of term is still to be worked on,
-- since it does not allow to use builtins or defined functions,
-- and it contains application of term to types,
-- A frequent situation in system F, but not allowed in the logic of SMT solvers.
translateTerm :: (LanguageSMT lang, ToSMT meta) => PrtTermMeta lang meta -> SmtLib.SExpr
translateTerm (App var args) = SmtLib.app (translateVar var) (translateArg <$> args)
translateTerm (Lam ann ty term) = error "Translate term to smtlib: Lambda abstraction in term"
translateTerm (Abs ann kind term) = error "Translate term to smtlib: Type abstraction in term"

translateVar :: (LanguageSMT lang, ToSMT meta) => PrtVarMeta lang meta -> SmtLib.SExpr
-- VCM: I actually think we shouldn't ever find a bound variable to be translated...
translateVar (B (Ann name) _) = SmtLib.symbol (toSmtName name)
translateVar (F (FreeName name)) = SmtLib.symbol (toSmtName name)
translateVar (F _) = error "Free variable translation not yet implemented."
translateVar (M h) = translate h

translateArg :: (LanguageSMT lang, ToSMT meta) => PrtArgMeta lang meta -> SmtLib.SExpr
translateArg (Arg term) = translateTerm term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
translateArg (TyArg ty) = translateType ty

-- | The definition of constructors in SMTlib follows a fixed layout. This
-- function translates constructor types in PlutusIR to this layout and
-- provides required names for the fields of product types.
constructorFromPIR ::
  forall lang meta .
  (LanguageSMT lang, ToSMT meta) =>
  (Name, PrtTypeMeta lang meta) ->
  (String, [(String, SmtLib.SExpr)])
constructorFromPIR (name, constructorType) =
  ( toSmtName name,
    -- Fields of product types must be named:
    -- we append ids to the constructor name
    zip
      ((toSmtName name ++) . ("_" ++) . show <$> [1 ..])
      (aux constructorType)
  )
  where
    aux :: PrtTypeMeta lang meta -> [SmtLib.SExpr]
    aux x = let (args, _) = tyFunArgs x in map translateType args
