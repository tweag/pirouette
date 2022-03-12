{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Pirouette.Transformations.EtaExpand(etaExpand) where

import Data.Bifunctor
import Data.Generics.Uniplate.Data
import qualified Data.Map as M
import Data.Maybe

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import Pirouette.Term.Syntax.SystemF

import Pirouette.Transformations.Utils

etaExpand :: forall lang. (PrettyLang lang, Pretty (FunDef lang Name), LanguageDef lang)
          => PrtUnorderedDefs lang
          -> PrtUnorderedDefs lang
etaExpand defs@PrtUnorderedDefs{..} = transformBi exp defs
  where
    exp :: PrtTerm lang -> PrtTerm lang
    exp src@(F (FreeName name) `App` args)
      | Just nameType <- lookupNameType prtUODecls name
      , specNameType <- nameType `appN` argsTy
      , (fullArgs, _) <- flattenType specNameType
      , remainingArgs <- drop (length args - length argsTy) fullArgs
      , let remArgsLen = fromIntegral $ length remainingArgs
      , remArgsLen > 0
        = wrapInLambdas remainingArgs $ F (FreeName name) `App` ((shiftArg remArgsLen <$> args) <> mkExpIndices remArgsLen)
      where 
        argsTy = mapMaybe fromTyArg args
    exp term = term

    mkExpIndices cnt = [ Arg $ B (Ann "η") idx `App` []
                       | idx <- reverse [0 .. cnt - 1]
                       ]

wrapInLambdas :: [FlatArgType lang] -> PrtTerm lang -> PrtTerm lang
wrapInLambdas types term = foldr f term types
  where
    f (FlatTyArg k) = Abs (Ann "η") k
    f (FlatTermArg ty) = Lam (Ann "η") ty

-- TODO have a proper @instance HasSubst (PrtArg lang)@ or smth similar
shiftArg :: Integer -> PrtArg lang -> PrtArg lang
shiftArg k (Arg e) = Arg $ shift k e
shiftArg k (TyArg t) = TyArg $ shift k t

-- | Returns the type of the given name.
--
-- This may return Nothing if the name is not known or
-- if the name doesn't have a *-inhabiting type (for instance, being a type itself).
lookupNameType :: Decls lang Name -> Name -> Maybe (PrtType lang)
lookupNameType decls name = name `M.lookup` decls >>= getName
  where
    getName (DFunDef fd) = Just $ funTy fd
    getName (DConstructor idx typeName) = do
      DTypeDef Datatype{..} <- typeName `M.lookup` decls   -- this pattern-match failure shall probably be a hard error instead of Nothing
      conTy <- constructors `safeIdx` idx
      pure $ foldr (\(name, kind) ty -> TyAll (Ann name) kind ty) (snd conTy) typeVariables
    getName (DDestructor na) = Nothing -- TODO just write the type of the destructor out
    getName (DTypeDef td) = Nothing

