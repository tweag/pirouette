{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Implements whole-program transformations. If you're looking
--  for term transformations, check "Pirouette.Term.Transformations"
module Pirouette.Transformations.Inline where

import Data.Generics.Uniplate.Operations
import Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Term

-- | Expand all non-recursive definitions in our state, keeping only the
--  recursive definitions or those satisfying the @keep@ predicate.
expandAllNonRec :: forall lang. (LanguageBuiltins lang) => (Name -> Bool) -> PrtOrderedDefs lang -> PrtOrderedDefs lang
expandAllNonRec keep prtDefs =
  let ds = prtDecls prtDefs
      ord = prtDepOrder prtDefs
      (remainingNames, ds', _inlinables) = foldl' go ([], ds, Map.empty) ord
   in PrtOrderedDefs ds' (reverse remainingNames)
  where
    -- The 'go' functions goes over the defined terms in dependency order
    -- and inlines terms as much as possible. To do so efficiently,
    -- we keep a map of inlinable definitions and we also maintain the order
    -- for the names that are left in the actual definitions.
    --
    -- In general, say that: (rNs, ds', rest) = foldl' go ([], decls, Map.empty) ord
    -- then, with a slight abuse of notation:
    --
    -- >    Map.union ds' rest == decls -- modulo beta equivalence
    -- > && Set.fromList rNs == Set.fromList (Map.keys ds')
    -- > && reverse rNs `isSubListOf` ord
    --
    go ::
      ([SystF.Arg Name Name], Decls lang, Map.Map Name (Term lang)) ->
      SystF.Arg Name Name ->
      ([SystF.Arg Name Name], Decls lang, Map.Map Name (Term lang))
    go (names, currDecls, inlinableDecls) (SystF.TyArg ty) = (SystF.TyArg ty : names, currDecls, inlinableDecls)
    go (names, currDecls, inlinableDecls) (SystF.TermArg k) =
      let (decls', kDef) = expandDefsIn inlinableDecls currDecls k
       in if SystF.TermArg k `Set.member` termNames kDef || keep k
            then (SystF.TermArg k : names, decls', inlinableDecls)
            else (names, Map.delete (TermNamespace, k) decls', Map.insert k kDef inlinableDecls)

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
