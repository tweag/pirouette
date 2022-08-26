{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Implements whole-program transformations. If you're looking
--  for term transformations, check "Pirouette.Term.Transformations"
module Pirouette.Transformations.Inline where

import Data.Generics.Uniplate.Operations
import qualified Data.Map as Map
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Term

expandDefsIn ::
  (LanguageBuiltins lang) =>
  Map.Map Name (Term lang) ->
  Decls lang ->
  Name ->
  (Decls lang, Term lang)
expandDefsIn inlinables decls k =
  case Map.lookup (TermNamespace, k) decls of
    Nothing -> error $ "expandDefsIn: term " ++ show k ++ " undefined in decls"
    Just (DFunction r t ty) ->
      let t' = deshadowBoundNames $ rewrite (inlineAll inlinables) t
       in (Map.insert (TermNamespace, k) (DFunction r t' ty) decls, t')
    Just _ -> error $ "expandDefsIn: term " ++ show k ++ " not a function"

inlineAll :: (LanguageBuiltins lang) => Map.Map Name (Term lang) -> Term lang -> Maybe (Term lang)
inlineAll inlinables (SystF.App (SystF.Free (TermSig n)) args) = do
  nDef <- Map.lookup n inlinables
  Just $ SystF.appN nDef args
inlineAll _ _ = Nothing
