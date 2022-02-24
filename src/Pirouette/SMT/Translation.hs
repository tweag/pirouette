{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

-- | Translation of Pirouette syntactical categories into
-- smtlib through our copy of the SimpleSMT library.
module Pirouette.SMT.Translation where

import Control.Monad.Except
import qualified Data.Map as Map
import Pirouette.Monad
import Pirouette.SMT.Base
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as Raw

-- * Translating Terms and Types to SMTLIB

-- | Checks whether we can translate the current datatype definitions and whether
--  the type of each term is amenable to translation. We won't try translating the terms
--  because these will contain bound variables that will need to be substituted by
--  the symbolic execution engine.
checkDefsToSMT :: (PirouetteReadDefs builtins m, PrettyLang builtins, LanguageSMT builtins) => m ()
checkDefsToSMT = do
  allDefs <- prtAllDefs
  forM_ (Map.toList allDefs) $ \(n, def) -> do
    case def of
      DFunction _red _term ty -> void $ translateType ty
      DTypeDef (Datatype _ _ _ constr) -> mapM_ constructorFromPIR constr
      _ -> return ()

translateTypeBase ::
  forall builtins m.
  (LanguageSMT builtins, MonadFail m) =>
  TypeBase builtins ->
  m SmtLib.SExpr
translateTypeBase (TyBuiltin pirType) = return $ translateBuiltinType @builtins pirType
translateTypeBase (TypeFromSignature name) = return $ SmtLib.symbol (toSmtName name)

translateType ::
  (LanguageSMT builtins, ToSMT meta, MonadFail m) =>
  TypeMeta builtins meta ->
  m SmtLib.SExpr
translateType (Raw.TyApp (Raw.Free ty) args) = SmtLib.app <$> translateTypeBase ty <*> mapM translateType args
translateType (Raw.TyApp (Raw.Bound (Raw.Ann ann) index) args) =
  SmtLib.app (SmtLib.symbol (toSmtName ann)) <$> mapM translateType args
translateType x = fail $ "Translate type to smtlib: cannot handle " <> show x

-- TODO: The translation of term is still to be worked on,
-- since it does not allow to use builtins or defined functions,
-- and it contains application of term to types,
-- A frequent situation in system F, but not allowed in the logic of SMT solvers.
translateTerm ::
  (LanguageSMT builtins, ToSMT meta, MonadFail m) =>
  TermMeta builtins meta ->
  m SmtLib.SExpr
translateTerm (Raw.App var args) = SmtLib.app <$> translateVar var <*> mapM translateArg args
translateTerm (Raw.Lam ann ty term) = fail "Translate term to smtlib: Lambda abstraction in term"
translateTerm (Raw.Abs ann kind term) = fail "Translate term to smtlib: Type abstraction in term"

translateVar ::
  forall builtins meta m.
  (LanguageSMT builtins, ToSMT meta, MonadFail m) =>
  VarMeta builtins meta ->
  m SmtLib.SExpr
translateVar (Raw.Meta h) = return $ translate h
translateVar (Raw.Free (TermFromSignature name)) = return $ SmtLib.symbol (toSmtName name)
translateVar (Raw.Free (Constant c)) = return $ translateConstant @builtins c
translateVar (Raw.Free (Builtin b)) = return $ translateBuiltinTerm @builtins b
translateVar (Raw.Bound (Raw.Ann name) _) = fail "translateVar: Bound variable; did you forget to apply something?"
translateVar (Raw.Free Bottom) = fail "translateVar: Bottom; unclear how to translate that. WIP"

translateArg ::
  (LanguageSMT builtins, ToSMT meta, MonadFail m) =>
  ArgMeta builtins meta ->
  m SmtLib.SExpr
translateArg (Raw.TermArg term) = translateTerm term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
translateArg (Raw.TyArg ty) = translateType ty

-- | The definition of constructors in SMTlib follows a fixed layout. This
-- function translates constructor types in PlutusIR to this layout and
-- provides required names for the fields of product types.
constructorFromPIR ::
  forall builtins meta m.
  (LanguageSMT builtins, ToSMT meta, MonadFail m) =>
  (Name, TypeMeta builtins meta) ->
  m (String, [(String, SmtLib.SExpr)])
constructorFromPIR (name, constructorType) =
  (toSmtName name,)
    .
    -- Fields of product types must be named: we append ids to the constructor name
    zip
      ((toSmtName name ++) . ("_" ++) . show <$> [1 ..])
    <$> aux constructorType
  where
    aux :: TypeMeta builtins meta -> m [SmtLib.SExpr]
    aux x = let (args, _) = Raw.tyFunArgs x in mapM translateType args
