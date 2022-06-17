module Pirouette.Transformations.Contextualize where

import qualified Data.Text as T
import qualified Data.Map as Map
import Pirouette.Monad
import Pirouette.Term.Syntax as S
import Pirouette.Term.Syntax.SystemF as SystF

-- | Make all the 'Name's in the term with empty uniques
-- refer to those in the context.
-- This is especially useful when working with lonely terms
-- created by the quasiquoter, but which ultimately need
-- to refer back to elements in a 'Program'.
contextualizeTerm :: (PirouetteReadDefs lang m) => Term lang -> m (Term lang)
contextualizeTerm tm = fixContextTerm <$> prtAllDefs <*> pure tm

-- | Make all the 'Name's in the type with empty uniques
-- refer to those in the context.
-- This is especially useful when working with lonely types
-- created by the quasiquoter, but which ultimately need
-- to refer back to elements in a 'Program'.
contextualizeType :: (PirouetteReadDefs lang m) => Type lang -> m (Type lang)
contextualizeType tm = fixContextType <$> prtAllDefs <*> pure tm

fixContextName :: FixContextElement -> Map.Map Name (Definition lang) -> Name -> Name
fixContextName elt inScope nm
  | Just _ <- nameUnique nm = nm  -- if it has a unique, don't change it
  | otherwise =
    let sameName = Map.filterWithKey (\k d -> nameString k == nameString nm && chooseElement elt d) inScope
    in case Map.size sameName of
      0 -> nm
      1 -> fst $ head $ Map.toList sameName  -- we know we have just one
      _ -> error $ "cannot fix " <> T.unpack (nameString nm)


fixContextTermVar :: Map.Map Name (Definition lang)
                  -> SystF.VarMeta meta ann (TermBase lang)
                  -> SystF.VarMeta meta ann (TermBase lang)
fixContextTermVar inScope (Free (TermSig nm)) = Free (TermSig (fixContextName FixTerm inScope nm))
fixContextTermVar _inScope other = other

fixContextTypeVar :: Map.Map Name (Definition lang)
                  -> SystF.VarMeta meta ann (TypeBase lang)
                  -> SystF.VarMeta meta ann (TypeBase lang)
fixContextTypeVar inScope (Free (TySig nm)) = Free (TySig (fixContextName FixType inScope nm))
fixContextTypeVar _inScope other = other

fixContextTerm :: Map.Map Name (Definition lang) -> Term lang -> Term lang
fixContextTerm inScope (App var args) =
  App (fixContextTermVar inScope var)
      [argMap (fixContextType inScope) (fixContextTerm inScope) arg | arg <- args]
fixContextTerm inScope (Abs var@(Ann this) ki body) = 
  let -- remove shadowed types from scope
      inScope' = removeFromScope FixType inScope this
  in Abs var ki (fixContextTerm inScope' body)
fixContextTerm inScope (Lam var@(Ann this) ty body) = 
  let -- remove shadowed terms from scope
      inScope' = removeFromScope FixTerm inScope this
  in Lam var (fixContextType inScope' ty) (fixContextTerm inScope' body)

fixContextType :: Map.Map Name (Definition lang) -> Type lang -> Type lang
fixContextType inScope (TyApp v args) =
  TyApp (fixContextTypeVar inScope v) [fixContextType inScope arg | arg <- args]
fixContextType inScope (TyFun a b) =
  TyFun (fixContextType inScope a) (fixContextType inScope b)
fixContextType inScope (TyLam var@(Ann this) ki rest) =
  let inScope' = removeFromScope FixType inScope this
  in TyLam var ki (fixContextType inScope' rest)
fixContextType inScope (TyAll var@(Ann this) ki rest) =
  let inScope' = removeFromScope FixType inScope this
  in TyAll var ki (fixContextType inScope' rest)

data FixContextElement = FixType | FixTerm

chooseElement :: FixContextElement -> Definition lang -> Bool
chooseElement FixType = isTypeDef
chooseElement FixTerm = not . isTypeDef

removeFromScope :: FixContextElement -> Map.Map Name (Definition lang) -> Name -> Map.Map Name (Definition lang)
removeFromScope elt inScope nm =
  Map.filterWithKey (\k d -> nameString k /= nameString nm && chooseElement elt d) inScope