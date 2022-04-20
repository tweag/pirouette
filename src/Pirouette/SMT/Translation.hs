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
import Debug.Trace (trace)
import Pirouette.Monad
import Pirouette.SMT.Base
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as Raw

-- useful during debugging
traceMe :: String -> a -> a
traceMe _ = id

-- traceMe = trace

-- * Translating Terms and Types to SMTLIB

-- | Checks whether we can translate the current datatype definitions and whether
--  the type of each term is amenable to translation. We won't try translating the terms
--  because these will contain bound variables that will need to be substituted by
--  the symbolic execution engine.
checkDefsToSMT ::
  (PirouetteReadDefs builtins m, LanguagePretty builtins, LanguageSMT builtins) =>
  ExceptT String m ()
checkDefsToSMT = do
  allDefs <- lift prtAllDefs
  forM_ (Map.toList allDefs) $ \(_n, def) -> do
    case def of
      DFunction _red _term ty -> void $ translateType ty
      DTypeDef (Datatype _ _ _ constr) -> mapM_ constructorFromPIR constr
      _ -> return ()

translateTypeBase ::
  forall lang m.
  (LanguageSMT lang, Monad m) =>
  TypeBase lang ->
  m SmtLib.SExpr
translateTypeBase (TyBuiltin pirType) = return $ translateBuiltinType @lang pirType
translateTypeBase (TySig name) = return $ SmtLib.symbol (toSmtName name)

translateType ::
  (LanguageSMT lang, ToSMT meta, Monad m) =>
  TypeMeta lang meta ->
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
  forall lang meta m.
  (LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  [Name] ->
  Maybe (TypeMeta lang meta) ->
  TermMeta lang meta ->
  ExceptT String m SmtLib.SExpr
translateTerm _ _ (Raw.Lam _ann _ty _term) =
  throwError "Translate term to smtlib: Lambda abstraction in term"
translateTerm _ _ (Raw.Abs _ann _kind _term) =
  throwError "Translate term to smtlib: Type abstraction in term"
translateTerm knownNames ty (Raw.App var args) = case var of
  -- error cases
  Raw.Bound (Raw.Ann _name) _ ->
    throwError "translateApp: Bound variable; did you forget to apply something?"
  Raw.Free Bottom ->
    throwError "translateApp: Bottom; unclear how to translate that. WIP"
  -- meta go to ToSMT
  Raw.Meta h -> SmtLib.app (translate h) <$> mapM (translateArg knownNames Nothing) args
  -- constants and builtins go to LanguageSMT
  Raw.Free (Constant c) ->
    if null args
      then return $ translateConstant @lang c
      else throwError "translateApp: Constant applied to arguments"
  Raw.Free (Builtin b) -> do
    translatedArgs <- mapM (translateArg knownNames Nothing) args
    case translateBuiltinTerm @lang b translatedArgs of
      Nothing -> throwError "translateApp: Built-in term applied to wrong # of args"
      Just t -> return t
  Raw.Free (TermSig name)
    | name `elem` knownNames -> do
      _ <- traceMe ("translateApp: " ++ show name) (return ())
      SmtLib.app (SmtLib.symbol (toSmtName name)) <$> mapM (translateArg knownNames Nothing) args
    | otherwise -> do
      _ <- traceMe ("translateApp: " ++ show name ++ "; " ++ show ty) (return ())

      -- we need to "inject" the errors from PirouetteBase
      -- into those of ExceptT
      defn <-
        ExceptT $
          catchError
            (Right <$> prtDefOf name)
            (\_ -> return $ Left $ "translateApp: Unknown name: " <> show name)

      case defn of
        DConstructor _ tname -> do
          tdef <- ExceptT $ catchError (Right . Just <$> prtTypeDefOf tname) (\_ -> return $ Right Nothing)
          -- we first need to figure out the real type
          let actualTy = case (ty, tdef) of
                (Just ty', _) -> Just ty'
                -- if there are no variables, we know the type in its entirety too
                (_, Just Datatype {typeVariables = []}) -> Just $ Raw.TyApp (Raw.Free (TySig name)) []
                _ -> Nothing
          -- now we push the types of the arguments, if known
          translatedArgs <- mapM (translateArg knownNames Nothing) args
          -- finally we build the
          case actualTy of
            Just ty' ->
              SmtLib.app
                <$> (SmtLib.as (SmtLib.symbol (toSmtName name)) <$> translateType ty')
                <*> pure translatedArgs
            Nothing ->
              pure $ SmtLib.app (SmtLib.symbol (toSmtName name)) translatedArgs
        DTypeDef _ ->
          throwError "translateApp: Type name in function name"
        DFunDef _ ->
          throwError $ "translateApp: Cannot handle '" <> show name <> "' yet"
        DDestructor _ ->
          throwError $ "translateApp: Cannot handle '" <> show name <> "' yet"

translateArg ::
  (LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  [Name] ->
  Maybe (TypeMeta lang meta) ->
  ArgMeta lang meta ->
  ExceptT String m SmtLib.SExpr
translateArg knownNames ty (Raw.TermArg term) = translateTerm knownNames ty term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
translateArg _ _ (Raw.TyArg ty) = translateType ty

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
