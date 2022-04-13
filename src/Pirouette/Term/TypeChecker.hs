{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
module Pirouette.Term.TypeChecker where

import Data.Bifunctor
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Pirouette.Term.Syntax.Base hiding (Var, TyVar)
import Pirouette.Term.Syntax.Pretty
import Pirouette.Term.Syntax.SystemF
import Pirouette.Term.Syntax.Subst (shift)
import Prettyprinter hiding (Pretty, pretty)

-- | Checks an entire set of declarations.
typeCheckDecls
  :: LanguageBuiltinTypes lang
  => Decls lang -> Either (TypeError lang) ()
typeCheckDecls decls = do
  _ <- flip Map.traverseWithKey decls $ \name decl -> case decl of
    DFunDef FunDef { funBody, funTy } ->
      flip runReaderT ((decls, []), [DeclPath name]) $
        void $ typeCheckTerm funTy funBody
    _ -> pure ()
  pure ()

-- | Checks a single function definition.
typeCheckFunDef
  :: LanguageBuiltinTypes lang
  => Decls lang -> Name -> FunDef lang -> Either (TypeError lang) ()
typeCheckFunDef decls nm FunDef { funBody, funTy } =
  flip runReaderT ((decls, []), [DeclPath nm]) $
    void $ typeCheckTerm funTy funBody

data TypeError lang
  = TypeError {
    typeErrorPath :: ErrorPath,
    typeErrorKind :: TypeErrorKind lang
  }
  deriving (Eq, Show)

type ErrorPath = [ErrorPathElement]

data ErrorPathElement
  = TypePathAppHead
  | TypePathAppArg Int
  | TypePathKind
  | TypePathBody
  | DeclPath Name
  | TermPathLambdaArg (Ann Name)
  | TermPathLambdaBody (Ann Name)
  | TermPathAbsArg (Ann Name)
  | TermPathAbsBody (Ann Name)
  | TermPathAppHead
  | TermPathAppTyArg Int
  | TermPathAppTermArg Int
  | TermPathAppResult
  deriving (Eq, Show)

type TyVar lang = Var Name (TypeBase lang)
type TermVar lang = Var Name (TermBase lang)

data TypeErrorKind lang
  = TypeAppDifferentHeads (Type lang) (Type lang)
  | TypeAppArgumentLength (Type lang) (Type lang)
  | TypeJustDifferent (Type lang) (Type lang)
  | KindJustDifferent Kind Kind
  | NameUnknown Name
  | BoundUnknown Integer
  | TermLambdaButNoFunction (Type lang)
  | TermAppExpectedTyFun (Type lang)
  | TermAppExpectedTyAll (Type lang)
  deriving (Eq, Show)

type TypeCheckerCtx lang m =
   ( LanguageBuiltinTypes lang, MonadError (TypeError lang) m
   , MonadReader ((Decls lang, [Type lang]), ErrorPath) m )

-- | Go within certain element during type checking.
within
  :: MonadReader (defs, ErrorPath) m
  => ErrorPathElement -> m a -> m a
within elt = local $ second (elt :)

-- | Error out with the given message.
-- The error path comes from the context.
err
  :: (MonadReader (defs, ErrorPath) m, MonadError (TypeError lang) m)
  => TypeErrorKind lang -> m a
err e = do
  (_, path) <- ask
  throwError (TypeError path e)

-- | Find a free name in the context.
typeOfFree
  :: TypeCheckerCtx lang m
  => Name -> m (Type lang)
typeOfFree nm = do
  ((decls, _), _) <- ask
  case Map.lookup nm decls of
    Just (DFunction _ _ ty) -> pure ty
    Just (DDestructor t) -> do
      tdef <- typeDef nm t
      pure $ destructorTypeFor t tdef
    Just (DConstructor i t) -> do
      tdef <- typeDef nm t
      case safeIx (constructors tdef) i of
        Just (_, ty) -> pure ty
        Nothing -> err $ NameUnknown nm
    _ -> err $ NameUnknown nm

-- | Find a type definition in the context.
typeDef
  :: TypeCheckerCtx lang m
  => Name -> Name -> m (TypeDef lang)
typeDef origin nm = do
  ((decls, _), _) <- ask
  case Map.lookup nm decls of
    Just (DTypeDef def) -> pure def
    _ -> err $ NameUnknown origin

-- | Find the type of a bound variable in the context.
typeOfBound
  :: TypeCheckerCtx lang m
  => Integer -> m (Type lang)
typeOfBound n = do
  ((_, bounds), _) <- ask
  case safeIx bounds n of
    Just ty -> pure ty
    Nothing -> err $ BoundUnknown n

-- | Introduce a bound element in the (local) context.
extendBound
  :: TypeCheckerCtx lang m
  => Type lang -> m a -> m a
extendBound ty = do
  local f
  where
    f ((decls, bounds), path) =
      ((decls, ty : bounds), path)

-- |When type-checking something like:
--
-- > /\ a : Type . \ x : a . /\ b : Type . \ y : b . M
--
-- The first time we see the @\x : a@ we register @x@ of
-- type @Bound 0@; but when we enter @M@, the type of @x@
-- is, in reality, @Bound 1@: passing through the second
-- 'Abs' needs to shift our declared bound variables accordingly.
shiftBoundTyVars
  :: TypeCheckerCtx lang m
  => m a -> m a
shiftBoundTyVars = local f
  where
    f ((decls, bounds), path) =
      ((decls, map (shift 1) bounds), path)

-- | Check that the given term has the given type.
-- Errors are given using the 'MonadError' interface.
typeCheckTerm
 :: TypeCheckerCtx lang m
 => Type lang -> Term lang -> m ()
typeCheckTerm ty (Lam x xTy body) =
  case ty of
    TyFun argTy resTy -> do
      within (TermPathLambdaArg x) $
        eqType argTy xTy
      within (TermPathLambdaBody x) $ do
        extendBound xTy $
          typeCheckTerm resTy body
    _ -> err $ TermLambdaButNoFunction ty
typeCheckTerm ty (Abs x ki body) =
  case ty of
    TyAll _ tyKi tyRest -> do
      within (TermPathAbsArg x) $
        eqKind tyKi ki
      within (TermPathAbsBody x) $
        shiftBoundTyVars $
          typeCheckTerm tyRest body
    _ -> err $ TermLambdaButNoFunction ty
typeCheckTerm ty (App hd args) = do
  hdTy <- within TermPathAppHead $ findType hd
  finalTy <- typeCheckArgs args hdTy 1
  within TermPathAppResult $ eqType ty finalTy
  where
    typeCheckArgs [] current _ = pure current
    typeCheckArgs (TyArg appliedTy : more) current n = do
      new <- within (TermPathAppTyArg n) $
        case current of
          goodTy@TyAll {} ->
            pure $ tyInstantiate goodTy appliedTy
          _ -> err $ TermAppExpectedTyAll current
      typeCheckArgs more new (n + 1)
    typeCheckArgs (TermArg tm : more) current n = do
      new <- within (TermPathAppTermArg n) $
        case current of
          TyFun tyArg tyRes -> do
            typeCheckTerm tyArg tm
            pure tyRes
          _ -> err $ TermAppExpectedTyFun current
      typeCheckArgs more new (n + 1)

-- | Find the type either in the context,
-- or in the built-in constants and terms.
findType
  :: TypeCheckerCtx lang m
  => Var Name (TermBase lang) -> m (Type lang)
findType (Bound _ i) =
  typeOfBound i
findType (Free (TermSig f)) =
  typeOfFree f
findType (Free (Constant c)) =
  pure $ typeOfConstant c
findType (Free (Builtin t)) =
  pure $ typeOfBuiltin t
findType (Free Bottom) =
  pure typeOfBottom
findType (Meta _) =
  error "this should never happen, meta is Void"

-- | Check equality of two types.
eqType
  :: TypeCheckerCtx lang m
  => Type lang -> Type lang -> m ()
eqType ty1@(TyApp h1 args1) ty2@(TyApp h2 args2) = do
  within TypePathAppHead $
    unless (eqVar h1 h2) $
      err $ TypeAppDifferentHeads ty1 ty2
  unless (length args1 == length args2) $
      err $ TypeAppArgumentLength ty1 ty2
  forM_ (zip3 [1 ..] args1 args2) $ \(i, arg1, arg2) ->
    within (TypePathAppArg i) $
      eqType arg1 arg2
eqType (TyFun arg1 res1) (TyFun arg2 res2) = do
  within (TypePathAppArg 1) $ eqType arg1 arg2
  within (TypePathAppArg 2) $ eqType res1 res2
eqType (TyLam _ ki1 ty1) (TyLam _ ki2 ty2) =
  eqTypeThatBinds ki1 ty1 ki2 ty2
eqType (TyAll _ ki1 ty1) (TyAll _ ki2 ty2) = do
  eqTypeThatBinds ki1 ty1 ki2 ty2
eqType ty1 ty2 = err $ TypeJustDifferent ty1 ty2

-- | Common code for TyLam and TyAll.
eqTypeThatBinds
  :: TypeCheckerCtx lang m
  => Kind -> Type lang -> Kind -> Type lang -> m ()
eqTypeThatBinds ki1 ty1 ki2 ty2 = do
  eqKind ki1 ki2
  within TypePathBody $
    eqType ty1 ty2  -- OK because we are using de Bruijn indices

-- | Check that two kinds are equal.
eqKind
  :: TypeCheckerCtx lang m
  => Kind -> Kind -> m ()
eqKind ki1 ki2 =
  within TypePathKind $
    unless (ki1 == ki2) $
      err $ KindJustDifferent ki1 ki2

-- | Check equality of variables.
-- Annotations on bound variables are not checked,
-- since we should just check their de Bruijn index.
eqVar
  :: LanguageBuiltins lang
  => Var Name (TypeBase lang) -> Var Name (TypeBase lang) -> Bool
eqVar (Bound _ i) (Bound _ j) = i == j
eqVar (Free f)    (Free g)    = f == g
eqVar (Meta _)    (Meta _)    = True -- here Meta is always Void
eqVar _           _           = False

safeIx
  :: (Eq n, Ord n, Num n)
  => [a]
  -> n
  -> Maybe a
safeIx [] _ = Nothing
safeIx (x : rest) n
  | n == 0    = pure x
  | n > 0     = safeIx rest (n - 1)
  | otherwise = Nothing

instance
  (LanguagePretty lang) =>
  Pretty (TypeError lang) where
  pretty TypeError { typeErrorPath, typeErrorKind } =
    vsep [ pretty typeErrorKind,
           "at" <+> encloseSep "" "" " -> " (map pretty path) ]
    where
      path = reverse $ dropWhile (== TermPathAppHead) typeErrorPath

instance Pretty ErrorPathElement where
  pretty TypePathAppHead = "cstr"
  pretty (TypePathAppArg n) = "arg" <+> pretty n
  pretty TypePathKind = "kind"
  pretty TypePathBody = "body"
  pretty (DeclPath na) = "definition of" <+> quoted na
  pretty (TermPathLambdaArg ann) = "\\" <> pretty ann
  pretty (TermPathLambdaBody ann) = "\\" <> pretty ann
  pretty (TermPathAbsArg ann) = "/\\" <> pretty ann
  pretty (TermPathAbsBody ann) = "/\\" <> pretty ann
  pretty TermPathAppHead = "fn"
  pretty (TermPathAppTyArg n) = "@arg" <+> pretty n
  pretty (TermPathAppTermArg n) = "arg" <+> pretty n
  pretty TermPathAppResult = "app result"

instance 
  (LanguagePretty lang) => 
  Pretty (TypeErrorKind lang) where
  pretty (TypeAppDifferentHeads ty1 ty2) = 
    prettyCouldNotMatchError ty1 ty2
  pretty (TypeAppArgumentLength ty1 ty2) = 
    prettyCouldNotMatchError ty1 ty2
  pretty (TypeJustDifferent ty1 ty2) =
    prettyCouldNotMatchError ty1 ty2
  pretty (KindJustDifferent ki1 ki2) = 
    prettyCouldNotMatchError ki1 ki2
  pretty (NameUnknown na) =
    "Unknown name" <+> quoted na
  pretty (BoundUnknown n) =
    "Unbound variable with level" <+> pretty n
  pretty (TermLambdaButNoFunction at) =
    "Expected function type but got" <+> quoted at
  pretty (TermAppExpectedTyFun at) =
    "Expected function type but got" <+> quoted at
  pretty (TermAppExpectedTyAll at) =
    "Expected quantified type but got" <+> quoted at

prettyCouldNotMatchError
  :: (Pretty a)
  => a -> a -> Doc ann
prettyCouldNotMatchError thing1 thing2 =
  "Couldn't match" <+> quoted thing1 <+> "with" <+> quoted thing2

quoted
  :: (Pretty a)
  => a -> Doc ann
quoted x = squotes (pretty x)