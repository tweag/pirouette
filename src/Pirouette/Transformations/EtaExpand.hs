{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.EtaExpand (etaExpandAll, etaExpandTerm) where

import Data.Generics.Uniplate.Data
import qualified Data.Map as M
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils

-- | Eta-expands all definitions of all terms involved in a program
etaExpandAll ::
  forall lang.
  (LanguagePretty lang, LanguageBuiltins lang) =>
  PrtUnorderedDefs lang ->
  PrtUnorderedDefs lang
etaExpandAll defs@PrtUnorderedDefs {..} = transformBi (etaExpandAux prtUODecls) defs

-- | Eta-expands a single term
etaExpandTerm ::
  forall lang m.
  (PirouetteReadDefs lang m, Language lang) =>
  Term lang ->
  m (Term lang)
etaExpandTerm t = do
  decls <- prtAllDefs
  return $ transformBi (etaExpandAux decls) t

-- | Given a type @t@ and a list of arguments @a1 ... aN@,
--  returns the type of a term @x : t@ partially applied to @a1 ... aN@.
--  This is different from type application because we need to instantiate
--  the 'SystF.TyAll's and drop the 'SystF.TyFun's.
instantiateType :: Type lang -> [Arg lang] -> Type lang
instantiateType t [] = t
instantiateType (SystF.TyFun _ u) (SystF.TermArg _ : args) = instantiateType u args
instantiateType (SystF.TyAll _ _ t) (SystF.TyArg arg : args) =
  instantiateType (subst (singleSub arg) t) args
instantiateType _ _ = error "instantiateType: type-checking would fail"

-- Auxiliar function, supposed to be used as an argument to 'transformBi' to
-- eta expand terms. Check 'etaExpandTerm' or 'etaExpandAll'.
etaExpandAux :: (LanguageBuiltins lang) => Decls lang -> Term lang -> Term lang
etaExpandAux decls (SystF.Free (TermSig name) `SystF.App` args)
  | Just nameType <- lookupNameType decls name,
    specNamePartialApp <- nameType `instantiateType` args,
    (remainingArgs, _) <- flattenType specNamePartialApp,
    -- After looking up the definition and infering its flattened type, we still have to
    -- separate between the arguments which are type arguments and which are term
    -- arguments:
    let remTyArgsLen = fromIntegral $ length $ filter isTyArg remainingArgs,
    let remTermArgsLen = fromIntegral $ length $ filter (not . isTyArg) remainingArgs,
    let remArgsLen = remTyArgsLen + remTermArgsLen,
    remArgsLen > 0 =
    wrapInLambdas remainingArgs $
      SystF.Free (TermSig name)
        `SystF.App` ( (shiftArg remTyArgsLen remTermArgsLen <$> args)
                        ++ mkExpIndices remTyArgsLen remTermArgsLen remainingArgs
                    )
  where
    -- Generating the arguments is simple; we fold over the list of remaining arguments
    -- and use either the mTy or the mTerm counters, then decrease whatever counter we
    -- used.
    mkExpIndices :: Integer -> Integer -> [FlatArgType lang] -> [Arg lang]
    mkExpIndices _ _ [] = []
    mkExpIndices mTy mTerm (FlatTyArg _ : as) =
      SystF.TyArg (SystF.tyPure $ SystF.Bound (SystF.Ann "H") (mTy - 1)) : -- H is capital η :)
      mkExpIndices (mTy - 1) mTerm as
    mkExpIndices mTy mTerm (FlatTermArg _ : as) =
      SystF.TermArg (SystF.termPure $ SystF.Bound (SystF.Ann "η") (mTerm - 1)) :
      mkExpIndices mTy (mTerm - 1) as
-- Any other term that is neither an application nor does it satisfy the guards above needs
-- no intervention; we just return it as is.
etaExpandAux _ term = term

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

-- | Returns the type of the given name.
--
-- This may return Nothing if the name is not known or
-- if the name doesn't have a *-inhabiting type (for instance, being a type itself).
lookupNameType :: Decls lang -> Name -> Maybe (Type lang)
lookupNameType decls name = name `M.lookup` decls >>= getName
  where
    getName (DFunDef fd) = Just $ funTy fd
    getName (DConstructor idx typeName) = do
      DTypeDef Datatype {..} <- typeName `M.lookup` decls -- this pattern-match failure shall probably be a hard error instead of Nothing
      conTy <- constructors `safeIdx` idx
      pure $ foldr (\(name', kind') ty -> SystF.TyAll (SystF.Ann name') kind' ty) (snd conTy) typeVariables
    getName (DDestructor _) = Nothing -- TODO just write the type of the destructor out
    getName (DTypeDef _) = Nothing
