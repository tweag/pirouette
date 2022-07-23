{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Transformations.Utils where

import Control.Arrow (first, (***))
import Data.Tuple
import Debug.Trace
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.SystemF hiding (Arg)
import qualified Pirouette.Term.Syntax.SystemF as SystF

traceDefsId :: (LanguagePretty lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
traceDefsId defs = renderSingleLineStr (pretty $ prtUODecls defs) `trace` defs

{-
type HOFDefs lang = M.Map (Namespace, Name) (HofDef lang)

findFuns ::
  LanguageBuiltins lang =>
  [((space, Name), Definition lang)] ->
  (FunDef lang -> Bool) ->
  [((space, Name), HofDef lang)]
findFuns declsPairs funPred =
  [ ((sp, name), HofDef name $ HDBFun funDef)
    | ((sp, name), DFunDef funDef) <- declsPairs,
      funPred funDef
  ]

-- | Find the types that satisfy a given predicate, additionally return all terms associated
--  with said types too: constructors and destructor.
findTypes ::
  LanguageBuiltins lang =>
  [((Namespace, Name), Definition lang)] ->
  (Name -> TypeDef lang -> Bool) ->
  [((Namespace, Name), HofDef lang)]
findTypes declsPairs tyPred =
  -- First we get the type definitions that satisfy the required predicate
  flip concatMap typeDefsSuchThat $ \(tyName, typeDef) ->
    -- Only now we add the rest of the relevant names; this is necessary because only @tyName@ belongs
    -- to 'TypeNamespace', the rest of the terms belong to 'TermNamespace'
    let spaceNames =
          (TypeNamespace, tyName) : [(TermNamespace, name) | name <- destructor typeDef : map fst (constructors typeDef)]
     in [((sp, name), HofDef tyName $ HDBType typeDef) | (sp, name) <- spaceNames]
  where
    typeDefsSuchThat = [(tyName, typeDef) | ((_, tyName), DTypeDef typeDef) <- declsPairs, tyPred tyName typeDef]

findHOFDefs ::
  forall lang.
  LanguageBuiltins lang =>
  (FunDef lang -> Bool) ->
  (Name -> TypeDef lang -> Bool) ->
  [((Namespace, Name), Definition lang)] ->
  HOFDefs lang
findHOFDefs funPred tyPred declsPairs =
  M.fromList $ findFuns declsPairs funPred' <> findTypes declsPairs tyPred'
  where
    funPred' :: FunDef lang -> Bool
    funPred' fun = funPred fun && hasHOFuns (funTy fun)
    tyPred' name typeDef = tyPred name typeDef && (hasHOFuns . snd) `any` constructors typeDef
-}

-- @Arg Kind (Type lang)@ could've been used here instead,
-- but having a distinct type seems to be a bit nicer, at least for now for hole-driven development reasons.
data FlatArgType lang
  = FlatTyArg Kind
  | FlatTermArg (Type lang)
  deriving (Show)

flattenType :: Type lang -> ([FlatArgType lang], Type lang)
flattenType ty@TyApp {} = ([], ty)
flattenType (dom `TyFun` cod) = first (FlatTermArg dom :) $ flattenType cod
flattenType (TyAll _ k ty) = first (FlatTyArg k :) $ flattenType ty
flattenType TyLam {} = error "unnormalized type"

-- | Splits a list of arguments into two lists:
-- the first one containing all arguments up to and including the last type argument,
-- and the second one containing the rest of the (term) arguments.
--
-- For example, on 'foo @ty1 term1 @ty2 term2 term3' it returns
-- '([@ty1, term1, @ty2], [term2, term3])'.
splitArgsTermsTail :: [SystF.Arg ty v] -> ([SystF.Arg ty v], [SystF.Arg ty v])
splitArgsTermsTail = swap . (reverse *** reverse) . span SystF.isArg . reverse

{-
-- This really belongs to a Pretty module, but we need them here for nicer debugging anyway for now.
instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HofDefBody lang) where
  pretty (HDBType defn) = "<typ>" <+> pretty defn
  pretty (HDBFun defn) = "<fun>" <+> pretty defn

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HofDef lang) where
  pretty = pretty . hofDefBody

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HOFDefs lang) where
  pretty = align . vsep . map (\(n, d) -> pretty n <+> pretty d) . M.toList
-}
