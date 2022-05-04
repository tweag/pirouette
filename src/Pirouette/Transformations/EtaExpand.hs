{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.EtaExpand (etaExpandAll, etaExpandTerm) where

import Control.Monad.Identity
import qualified Data.Map as M
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils

-- | Eta-expands all definitions of all terms involved in a program
etaExpandAll ::
  forall lang.
  (LanguageBuiltinTypes lang, Language lang) =>
  PrtUnorderedDefs lang ->
  PrtUnorderedDefs lang
etaExpandAll PrtUnorderedDefs {..} =
  PrtUnorderedDefs
    { prtUODecls = M.map (runIdentity . defTermMapM (return . go)) prtUODecls,
      prtUOMainTerm = go prtUOMainTerm
    }
  where
    go = etaExpandAux prtUODecls []

-- | Eta-expands a single term
etaExpandTerm ::
  forall lang m.
  (PirouetteReadDefs lang m, LanguageBuiltinTypes lang, Language lang) =>
  Term lang ->
  m (Term lang)
etaExpandTerm t = do
  decls <- prtAllDefs
  return $ etaExpandAux decls [] t

-- | Given a type @t@ and a list of arguments @a1 ... aN@,
--  returns the type of a term @x : t@ partially applied to @a1 ... aN@.
--  This is different from type application because we need to instantiate
--  the 'SystF.TyAll's and drop the 'SystF.TyFun's.
instantiateType :: (Language lang) => Type lang -> [Arg lang] -> Type lang
instantiateType t [] = t
instantiateType (SystF.TyFun _ u) (SystF.TermArg _ : args) = instantiateType u args
instantiateType (SystF.TyAll _ _ t) (SystF.TyArg arg : args) =
  instantiateType (subst (singleSub arg) t) args
instantiateType t args =
  error $
    unlines
      [ "instantiateType: trying to instantiate:",
        "t = " ++ renderSingleLineStr (pretty t),
        "with",
        "args = " ++ renderSingleLineStr (pretty args)
      ]

-- Actual eta expansion definition; this needs to be a primitive recursive function
-- because we need to eta-expand arguments too.
etaExpandAux :: (Language lang, LanguageBuiltinTypes lang) => Decls lang -> [Type lang] -> Term lang -> Term lang
etaExpandAux decls env (SystF.Lam ann ty t) = SystF.Lam ann ty (etaExpandAux decls (ty : env) t)
etaExpandAux decls env (SystF.Abs ann k t) = SystF.Abs ann k (etaExpandAux decls env t)
etaExpandAux decls env (hd `SystF.App` args) =
  let args' = map (SystF.argMap id $ etaExpandAux decls env) args
   in case findType decls env hd of
        Just nameType ->
          let specNamePartialApp = nameType `instantiateType` args'
              (remainingArgs, _) = flattenType specNamePartialApp
              -- After looking up the definition and infering its flattened type, we still have to
              -- separate between the arguments which are type arguments and which are term
              -- arguments:
              remTyArgsLen = fromIntegral $ length $ filter isTyArg remainingArgs
              remTermArgsLen = fromIntegral $ length $ filter (not . isTyArg) remainingArgs
              remArgsLen = remTyArgsLen + remTermArgsLen
           in if remArgsLen > 0
                then
                  wrapInLambdas remainingArgs $
                    -- Because the 'hd' can be a bound variable; it might need to be shifted to
                    varMap (+ remTermArgsLen) hd
                      `SystF.App` ( (shiftArg remTyArgsLen remTermArgsLen <$> args')
                                      ++ mkExpIndices remTyArgsLen remTermArgsLen remainingArgs
                                  )
                else hd `SystF.App` args'
        Nothing -> error $ "etaExpandAux: " ++ show hd ++ " has no type"
  where
    -- Generating the arguments is simple; we fold over the list of remaining arguments
    -- and use either the mTy or the mTerm counters, then decrease whatever counter we
    -- used.
    mkExpIndices :: Integer -> Integer -> [FlatArgType lang] -> [Arg lang]
    mkExpIndices _ _ [] = []
    mkExpIndices mTy mTerm (FlatTyArg _ : as) =
      SystF.TyArg (SystF.TyPure $ SystF.Bound (SystF.Ann "H") (mTy - 1)) : -- H is capital η :)
      mkExpIndices (mTy - 1) mTerm as
    mkExpIndices mTy mTerm (FlatTermArg _ : as) =
      SystF.TermArg (SystF.termPure $ SystF.Bound (SystF.Ann "η") (mTerm - 1)) :
      mkExpIndices mTy (mTerm - 1) as

isTyArg :: FlatArgType lang -> Bool
isTyArg (FlatTyArg _) = True
isTyArg _ = False

wrapInLambdas :: [FlatArgType lang] -> Term lang -> Term lang
wrapInLambdas types term = foldr f term types
  where
    f (FlatTyArg k) = SystF.Abs (SystF.Ann "η") k
    f (FlatTermArg ty) = SystF.Lam (SystF.Ann "η") ty

-- TODO have a proper @instance HasSubst (Arg lang)@ or smth similar
shiftArg :: (LanguageBuiltins lang) => Integer -> Integer -> Arg lang -> Arg lang
shiftArg kTy kTerm (SystF.TermArg e) = SystF.TermArg $ SystF.termTyMap (shift kTy) $ shift kTerm e
shiftArg kTy _ (SystF.TyArg t) = SystF.TyArg $ shift kTy t

-- TODO: This was mostly copied from our type-checker; but it really seems like `PirouetteReadDefs`
-- should be extended to something like `PirouetteTyped`, which provides us these things

findType ::
  (LanguageBuiltinTypes lang) =>
  Decls lang ->
  [Type lang] ->
  Var lang ->
  Maybe (Type lang)
findType decls _env (SystF.Free (TermSig f)) =
  case M.lookup f decls of
    Just (DFunction _ _ ty) -> pure ty
    Just (DDestructor t) -> do
      tdef <- typeDef decls t
      pure $ destructorTypeFor t tdef
    Just (DConstructor i t) -> do
      tdef <- typeDef decls t
      case safeIdx (constructors tdef) i of
        Just (_, ty) -> pure ty
        Nothing -> Nothing
    _ -> Nothing
findType _decls _env (SystF.Free (Constant c)) = pure $ typeOfConstant c
findType _decls _env (SystF.Free (Builtin t)) = pure $ typeOfBuiltin t
findType _decls _env (SystF.Free Bottom) = pure typeOfBottom
findType _decls env (SystF.Bound _ i) = env `safeIdx` i
findType _decls _env (SystF.Meta _) =
  error "this should never happen, meta is Void"

typeDef ::
  Decls lang ->
  Name ->
  Maybe (TypeDef lang)
typeDef decls nm = do
  case M.lookup nm decls of
    Just (DTypeDef def) -> pure def
    _ -> Nothing
