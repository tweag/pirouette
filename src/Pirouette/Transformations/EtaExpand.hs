{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.EtaExpand (etaExpandAll, etaExpandTerm) where

import Data.Generics.Uniplate.Data
import Data.List
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

-- Auxiliar function, supposed to be used as an argument to 'transformBi' to
-- eta expand terms. Check 'etaExpandTerm' or 'etaExpandAll'.
etaExpandAux :: Decls lang -> Term lang -> Term lang
etaExpandAux decls (SystF.Free (TermSig name) `SystF.App` args)
  | Just nameType <- lookupNameType decls name,
    specNameType <- foldl' SystF.tyAfterTermApp nameType args,
    (remainingArgs, _) <- flattenType specNameType,
    let remArgsLen = fromIntegral $ length remainingArgs,
    remArgsLen > 0 =
    wrapInLambdas remainingArgs $
      SystF.Free (TermSig name)
        `SystF.App` ( (shiftArg remArgsLen <$> args)
                        <> mkExpIndices remainingArgs
                    )
  where
    mkExpIndices argList =
      let (nbTypeArg, nbTermArg) = countArgs argList
       in -- Since the de Bruijn indices are counted from 0,
          -- we decrease by one the number of arguments to get the de Bruijn to use.
          go argList (nbTypeArg - 1) (nbTermArg - 1)
      where
        countArgs l =
          foldl'
            ( \(nbTy, nbTe) x ->
                case x of
                  FlatTyArg {} -> (nbTy + 1, nbTe)
                  FlatTermArg {} -> (nbTy, nbTe + 1)
            )
            (0, 0)
            l

        go [] (-1) (-1) = []
        go [] _ _ = error "Number of expected arguments does not match."
        go (FlatTyArg {} : tl) nbTy nbTe =
          SystF.TyArg (SystF.Bound (SystF.Ann "η") nbTy `SystF.TyApp` []) :
          go tl (nbTy - 1) nbTe
        go (FlatTermArg {} : tl) nbTy nbTe =
          SystF.TermArg (SystF.Bound (SystF.Ann "η") nbTe `SystF.App` []) :
          go tl nbTy (nbTe - 1)
etaExpandAux _ term = term

wrapInLambdas :: [FlatArgType lang] -> Term lang -> Term lang
wrapInLambdas types term = foldr f term types
  where
    f (FlatTyArg k) = SystF.Abs (SystF.Ann "η") k
    f (FlatTermArg ty) = SystF.Lam (SystF.Ann "η") ty

-- TODO have a proper @instance HasSubst (Arg lang)@ or smth similar
shiftArg :: Integer -> Arg lang -> Arg lang
shiftArg k (SystF.TermArg e) = SystF.TermArg $ shift k e
shiftArg k (SystF.TyArg t) = SystF.TyArg $ shift k t

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
