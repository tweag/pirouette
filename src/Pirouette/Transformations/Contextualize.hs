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
-- to refer back to elements in a 'Program'. In particular, the `nameUnique` part might need adjustments.
-- Say you called the quasiquoter with @[pir| \x : Integer -> fib x |]@, you'd want `fib` to refers to something 
-- from the context. The `fib` in the context will actually be called @Name "fib" (Just u)@, where `u` is a 
-- unique identifier but the `fib` that came from the quasiquoter will be @Name "fib" Nothing@, hence we
-- need to adjust the 'nameUnique' portions.
contextualizeTerm :: (PirouetteReadDefs lang m) => Term lang -> m (Term lang)
contextualizeTerm tm = fixContextTerm <$> prtAllDefs <*> pure tm

-- | Make all the 'Name's in the type with empty uniques
-- refer to those in the context.
-- This is especially useful when working with lonely types
-- created by the quasiquoter, but which ultimately need
-- to refer back to elements in a 'Program'.
contextualizeType :: (PirouetteReadDefs lang m) => Type lang -> m (Type lang)
contextualizeType tm = fixContextType <$> prtAllDefs <*> pure tm

-- | Make a 'Name's in the type with empty uniques
-- refer to those in the context.
contextualizeTermName :: (PirouetteReadDefs lang m) => T.Text -> m Name
contextualizeTermName nm = fixContextName <$> prtAllDefs <*> pure TermNamespace <*> pure (Name nm Nothing)

-- | Make a 'Name's in the type with empty uniques
-- refer to those in the context.
resolve :: (PirouetteReadDefs lang m) => T.Text -> m Name
resolve = contextualizeTermName

fixContextName :: Map.Map (Namespace, Name) (Definition lang) -> Namespace -> Name -> Name
fixContextName inScope space nm
  | Just _ <- nameUnique nm = nm  -- if it has a unique, don't change it
  | otherwise =
    let sameName = Map.filterWithKey (\(s, k) _ -> nameString k == nameString nm && s == space) inScope
    in case Map.size sameName of
      0 -> nm
      1 -> snd $ fst $ head $ Map.toList sameName  -- we know we have just one
      _ -> error $ "cannot fix " <> T.unpack (nameString nm)


fixContextTermVar :: Map.Map (Namespace, Name) (Definition lang)
                  -> SystF.VarMeta meta ann (TermBase lang)
                  -> SystF.VarMeta meta ann (TermBase lang)
fixContextTermVar inScope (Free (TermSig nm)) = Free (TermSig (fixContextName inScope TermNamespace nm))
fixContextTermVar _inScope other = other

fixContextTypeVar :: Map.Map (Namespace, Name) (Definition lang)
                  -> SystF.VarMeta meta ann (TypeBase lang)
                  -> SystF.VarMeta meta ann (TypeBase lang)
fixContextTypeVar inScope (Free (TySig nm)) = Free (TySig (fixContextName inScope TypeNamespace nm))
fixContextTypeVar _inScope other = other

fixContextTerm :: Map.Map (Namespace, Name) (Definition lang) -> Term lang -> Term lang
fixContextTerm inScope (App var args) =
  App (fixContextTermVar inScope var)
      [argMap (fixContextType inScope) (fixContextTerm inScope) arg | arg <- args]
fixContextTerm inScope (Abs var@(Ann this) ki body) = 
  let -- remove shadowed types from scope
      inScope' = removeFromScope inScope TypeNamespace this
  in Abs var ki (fixContextTerm inScope' body)
fixContextTerm inScope (Lam var@(Ann this) ty body) = 
  let -- remove shadowed terms from scope
      inScope' = removeFromScope inScope TermNamespace this
  in Lam var (fixContextType inScope' ty) (fixContextTerm inScope' body)

fixContextType :: Map.Map (Namespace, Name) (Definition lang) -> Type lang -> Type lang
fixContextType inScope (TyApp v args) =
  TyApp (fixContextTypeVar inScope v) [fixContextType inScope arg | arg <- args]
fixContextType inScope (TyFun a b) =
  TyFun (fixContextType inScope a) (fixContextType inScope b)
fixContextType inScope (TyLam var@(Ann this) ki rest) =
  let inScope' = removeFromScope inScope TypeNamespace this
  in TyLam var ki (fixContextType inScope' rest)
fixContextType inScope (TyAll var@(Ann this) ki rest) =
  let inScope' = removeFromScope inScope TypeNamespace this
  in TyAll var ki (fixContextType inScope' rest)

removeFromScope :: Map.Map (Namespace, Name) (Definition lang)
                -> Namespace -> Name
                -> Map.Map (Namespace, Name) (Definition lang)
removeFromScope inScope space nm =
  Map.delete (space, nm) inScope