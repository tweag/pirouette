{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with maybe" #-}

-- | Translation of Pirouette syntactical categories into
-- smtlib through our copy of the SimpleSMT library.
module Pirouette.SMT.Translation where

import Control.Monad.Except
import qualified Data.Map as Map
import Pirouette.Monad
import Pirouette.SMT.Base
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as Raw

-- * Translating Terms and Types to SMTLIB

-- | Checks whether we can translate the current datatype definitions and whether
--  the type of each term is amenable to translation. We won't try translating the terms
--  because these will contain bound variables that will need to be substituted by
--  the symbolic execution engine.
checkDefsToSMT :: (PirouetteReadDefs builtins m, LanguagePretty builtins, LanguageSMT builtins) => ExceptT String m ()
checkDefsToSMT = do
  allDefs <- lift prtAllDefs
  forM_ (Map.toList allDefs) $ \(_n, def) -> do
    case def of
      DFunction _red _term ty -> void $ translateType ty
      DTypeDef (Datatype _ _ _ constr) -> mapM_ constructorFromPIR constr
      _ -> return ()

translateTypeBase ::
  forall builtins m.
  (LanguageSMT builtins, Monad m) =>
  TypeBase builtins ->
  m SmtLib.SExpr
translateTypeBase (TyBuiltin pirType) = return $ translateBuiltinType @builtins pirType
translateTypeBase (TySig name) = return $ SmtLib.symbol (toSmtName name)

translateType ::
  (LanguageSMT builtins, ToSMT meta, Monad m) =>
  TypeMeta builtins meta ->
  ExceptT String m SmtLib.SExpr
translateType (Raw.TyApp (Raw.Free ty) args) = 
  SmtLib.app <$> translateTypeBase ty <*> mapM translateType args
translateType (Raw.TyApp (Raw.Bound (Raw.Ann ann) _index) args) =
  SmtLib.app (SmtLib.symbol (toSmtName ann)) <$> mapM translateType args
translateType x = 
  throwError $ "Translate type to smtlib: cannot handle " <> show x

-- TODO: The translation of term is still to be worked on,
-- since it does not allow to use lang or defined functions,
-- and it contains application of term to types,
-- A frequent situation in system F, but not allowed in the logic of SMT solvers.
translateTerm ::
  (LanguageSMT builtins, ToSMT meta, Monad m) =>
  [Name] ->
  TermMeta builtins meta ->
  ExceptT String m SmtLib.SExpr
translateTerm knownNames (Raw.App var args) = do
  translatedArgs <- mapM (translateArg knownNames) args
  translateApp knownNames var translatedArgs
translateTerm _ (Raw.Lam _ann _ty _term) = 
  throwError "Translate term to smtlib: Lambda abstraction in term"
translateTerm _ (Raw.Abs _ann _kind _term) = 
  throwError "Translate term to smtlib: Type abstraction in term"

translateApp ::
  forall builtins meta m.
  (LanguageSMT builtins, ToSMT meta, Monad m) =>
  [Name] ->
  VarMeta builtins meta ->
  [SmtLib.SExpr] ->
  ExceptT String m SmtLib.SExpr
translateApp _ (Raw.Meta h) args = 
  pure $ SmtLib.app (translate h) args

translateApp knownNames (Raw.Free (TermSig name)) args = do
  guard (name `elem` knownNames)
  pure $ SmtLib.app (SmtLib.symbol (toSmtName name)) args

translateApp _ (Raw.Free (Constant c)) [] = 
  return $ translateConstant @builtins c
translateApp _ (Raw.Free (Constant _)) _ =
  throwError "translateVar: Constant applied to arguments"

translateApp _ (Raw.Free (Builtin b)) args =
  case translateBuiltinTerm @builtins b args of
    Nothing -> throwError "translateVar: Built-in term applied to wrong # of args"
    Just t  -> return t

translateApp _ (Raw.Bound (Raw.Ann _name) _) _ = 
  throwError "translateVar: Bound variable; did you forget to apply something?"
translateApp _ (Raw.Free Bottom) _ = 
  throwError "translateVar: Bottom; unclear how to translate that. WIP"

translateArg ::
  (LanguageSMT builtins, ToSMT meta, Monad m) =>
  [Name] ->
  ArgMeta builtins meta ->
  ExceptT String m SmtLib.SExpr
translateArg knownNames (Raw.TermArg term) = translateTerm knownNames term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
translateArg _ (Raw.TyArg ty) = translateType ty

-- | The definition of constructors in SMTlib follows a fixed layout. This
-- function translates constructor types in PlutusIR to this layout and
-- provides required names for the fields of product types.
constructorFromPIR ::
  forall builtins meta m.
  (LanguageSMT builtins, ToSMT meta, Monad m) =>
  (Name, TypeMeta builtins meta) ->
  ExceptT String m (String, [(String, SmtLib.SExpr)])
constructorFromPIR (name, constructorType) = do
  -- Fields of product types must be named: we append ids to the constructor name
  let fieldNames = map (((toSmtName name ++ "_") ++) . show) [1 :: Int ..]
  cstrs <- zip fieldNames <$> aux constructorType
  return (toSmtName name, cstrs)
  where
    aux :: TypeMeta builtins meta -> ExceptT String m [SmtLib.SExpr]
    aux x = let (args, _) = Raw.tyFunArgs x in mapM translateType args
