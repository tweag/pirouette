{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with maybe" #-}

-- | Translation of Pirouette syntactical categories into
-- smtlib through our copy of the SimpleSMT library.
module Pirouette.SMT.Translation where

import Control.Monad.Except
import Control.Monad.Writer (Any (..), WriterT (..), tell)
-- import Debug.Trace (trace)
import Pirouette.Monad
import Pirouette.SMT.Base
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as Raw

-- useful during debugging
traceMe :: String -> a -> a
traceMe _ = id

-- traceMe = trace

-- | Synonym which takes into account whether
-- the translation used any uninterpreted functions.
type UsedAnyUFs = Any

pattern UsedSomeUFs, NotUsedAnyUFs :: UsedAnyUFs
pattern UsedSomeUFs = Any True
pattern NotUsedAnyUFs = Any False

{-# COMPLETE UsedSomeUFs, NotUsedAnyUFs #-}

-- | Monad stack used for translation.
type TranslatorT m = WriterT UsedAnyUFs (ExceptT String m)

runTranslator :: TranslatorT m a -> m (Either String (a, UsedAnyUFs))
runTranslator = runExceptT . runWriterT

pattern TranslatorT :: m (Either e (a, w)) -> WriterT w (ExceptT e m) a
pattern TranslatorT x = WriterT (ExceptT x)

liftTranslator ::
  MonadError s m =>
  String ->
  m a ->
  TranslatorT m a
liftTranslator errorMessage action =
  TranslatorT $
    catchError
      (Right . (,NotUsedAnyUFs) <$> action)
      (\_ -> return $ Left errorMessage)

liftTranslatorMaybe ::
  MonadError s m =>
  m a ->
  TranslatorT m (Maybe a)
liftTranslatorMaybe action =
  TranslatorT $
    catchError
      (Right . (,NotUsedAnyUFs) . Just <$> action)
      (\_ -> return $ Right (Nothing, NotUsedAnyUFs))

-- * Translating Terms and Types to SMTLIB

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
  TranslatorT m SmtLib.SExpr
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
  TermMeta lang meta ->
  TranslatorT m SmtLib.SExpr
translateTerm _ (Raw.Lam _ann _ty _term) =
  throwError "Translate term to smtlib: Lambda abstraction in term"
translateTerm _ (Raw.Abs _ann _kind _term) =
  throwError "Translate term to smtlib: Type abstraction in term"
translateTerm knownNames (Raw.App var args) = case var of
  -- error cases
  Raw.Bound (Raw.Ann _name) _ ->
    throwError "translateApp: Bound variable; did you forget to apply something?"
  Raw.Free Bottom ->
    throwError "translateApp: Bottom; unclear how to translate that. WIP"
  -- meta go to ToSMT
  Raw.Meta h -> SmtLib.app (translate h) <$> mapM (translateArg knownNames) args
  -- constants and builtins go to LanguageSMT
  Raw.Free (Constant c) ->
    if null args
      then return $ translateConstant @lang c
      else throwError "translateApp: Constant applied to arguments"
  Raw.Free (Builtin b) -> do
    translatedArgs <- mapM (translateArg knownNames) args
    case translateBuiltinTerm @lang b translatedArgs of
      Nothing -> throwError "translateApp: Built-in term applied to wrong # of args"
      Just t -> return t
  Raw.Free (TermSig name) -> do
    _ <- traceMe ("translateApp: " ++ show name) (return ())
    defn <- liftTranslator ("translateApp: Unknown name: " <> show name) (prtDefOf name)
    case defn of
      DConstructor ix tname
        | name `notElem` knownNames ->
          throwError $ "translateApp: Unknown constructor '" <> show name <> "'"
        | otherwise -> do
          -- bring in the type information
          Datatype {constructors} <-
            liftTranslator
              ("translateApp: Unknown type '" <> show tname <> "'")
              (prtTypeDefOf tname)
          -- we assume that if everything is well-typed
          -- the constructor actually exists, hence the use of (!!)
          let cstrTy = snd (constructors !! ix)
              -- now we split the arguments as required for the constructor
              (tyArgs, restArgs) = splitAt (Raw.tyPolyArity cstrTy) args
              -- and instantiate the type
              instTy = Raw.tyInstantiateN (typeToMeta cstrTy) (map (\(Raw.TyArg ty) -> ty) tyArgs)
              (argTys, resultTy) = Raw.tyFunArgs instTy
          -- there must be exactly as many arguments as required
          guard (length argTys == length restArgs)
          -- finally build the term
          SmtLib.app
            <$> (SmtLib.as (SmtLib.symbol (toSmtName name)) <$> translateType resultTy)
            <*> mapM (translateArg knownNames) restArgs
      -- SmtLib.app (SmtLib.symbol (toSmtName name)) <$> mapM (translateArg knownNames) restArgs
      DFunDef _
        | name `notElem` knownNames ->
          throwError $ "translateApp: Unknown function '" <> show name <> "'"
        | otherwise -> do
          tell UsedSomeUFs
          SmtLib.app (SmtLib.symbol (toSmtName name)) <$> mapM (translateArg knownNames) args
      DTypeDef _ ->
        throwError "translateApp: Type name in function name"
      -- DO NEVER TRY TO TRANSLATE THESE!!
      -- even though SMT contains a match primitive,
      -- this should be taken care of at the level
      -- or symbolic evaluation instead
      DDestructor _ ->
        throwError $ "translateApp: Cannot handle '" <> show name <> "' yet"

translateArg ::
  (LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  [Name] ->
  ArgMeta lang meta ->
  TranslatorT m SmtLib.SExpr
translateArg knownNames (Raw.TermArg term) = translateTerm knownNames term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
translateArg _ (Raw.TyArg ty) = translateType ty

-- | The definition of constructors in SMTlib follows a fixed layout. This
-- function translates constructor types in PlutusIR to this layout and
-- provides required names for the fields of product types.
constructorFromPIR ::
  forall builtins meta typeVariable m.
  (LanguageSMT builtins, ToSMT meta, Monad m) =>
  [typeVariable] ->
  (Name, TypeMeta builtins meta) ->
  TranslatorT m (String, [(String, SmtLib.SExpr)])
constructorFromPIR tyVars (name, constructorType) = do
  -- Fields of product types must be named: we append ids to the constructor name
  let fieldNames = map (((toSmtName name ++ "_") ++) . show) [1 :: Int ..]
      (_, unwrapped) = Raw.tyUnwrapBinders (length tyVars) constructorType
      (args, _) = Raw.tyFunArgs unwrapped
  cstrs <- zip fieldNames <$> mapM translateType args
  return (toSmtName name, cstrs)
