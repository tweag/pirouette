{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.DCE where

import Control.Arrow (second)
import Data.Generics.Uniplate.Data
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils

data CtorRemoveInfo = CtorRemoveInfo
  { criCtorTypeName :: Name
  , criCtorName :: Name
  , criCtorIdx :: Int
  , criDtorName :: Name
  } deriving (Show, Eq, Ord)

newtype RemoveDeadCtorsOpts = RemoveDeadCtorsOpts
  { rdcoToKeep :: M.Map T.Text [T.Text]
  } deriving (Show)

removeDeadCtors :: forall lang. (Language lang)
                => RemoveDeadCtorsOpts
                -> PrtUnorderedDefs lang
                -> PrtUnorderedDefs lang
removeDeadCtors RemoveDeadCtorsOpts{..} defs = L.foldl' (flip removeCtor) defs ctorsToRemove
  where
    ctorsToRemove = filter (not . shallKeep) $ findDeadCtors defs

    shallKeep CtorRemoveInfo{..}
      | Just tyWhiteList <- nameString criCtorTypeName `M.lookup` rdcoToKeep = nameString criCtorName `elem` tyWhiteList
    -- If we don't have any whitelist record for the type, we keep its constructors unconditionally:
    -- removal of a type's constructors should be a very conscious and explicit decision by the user.
    shallKeep _ = True

-- | Finds the constructors that aren't used in the program.
--
-- Returns them in the reverse order of appearance in each individual data type.
-- This ordering allows removing constructors one after another, since each removed ctor
-- won't shift/invalidate the indexes of the subsequent ones.
findDeadCtors :: forall lang. (Language lang) => PrtUnorderedDefs lang -> [CtorRemoveInfo]
findDeadCtors defs = L.sortOn (negate . criCtorIdx) $ M.elems unusedCtors
  where
    ctorNameMap = M.fromList [ ((tyName, idx), ctorName)
                             | ((_, ctorName), DConstructor idx tyName) <- M.toList $ prtUODecls defs
                             ]
    allCtors = M.fromList [ (ctorName, CtorRemoveInfo{..})
                          | ((_, criCtorTypeName), DTypeDef td) <- M.toList $ prtUODecls defs
                          , let criDtorName = destructor td
                          , (criCtorIdx, (ctorName, _)) <- zip [0..] $ constructors td
                          , let criCtorName = ctorNameMap M.! (criCtorTypeName, criCtorIdx)
                          ]
    usedNames = S.fromList [ name | TermSig name <- universeBi defs :: [TermBase lang] ]
    unusedCtors = M.filterWithKey (\ctorName _ -> ctorName `S.notMember` usedNames) allCtors

-- | Removes the constructor with the given index of the given type from the program.
--
-- This removes both the constructor definition as well as
-- the corresponding branches in the calls to the type's destructor.
-- This also updates the definitions for the subsequent constructors to have the right (decremented) index.
removeCtor :: forall lang. (Language lang)
           => CtorRemoveInfo
           -> PrtUnorderedDefs lang
           -> PrtUnorderedDefs lang
removeCtor CtorRemoveInfo{..} = updateMatchers . shiftSubsequentCtorsDefs . updateTypeDef . removeCtorDef
  where
    removeCtorDef defs = defs {prtUODecls = M.filter (/= DConstructor criCtorIdx criCtorTypeName) $ prtUODecls defs}

    updateTypeDef defs = defs {prtUODecls = fixup <$> prtUODecls defs}
      where
        fixup (DTypeDef td)
          | destructor td == criDtorName = DTypeDef td {constructors = removeAt criCtorIdx $ constructors td}
        fixup d = d

    shiftSubsequentCtorsDefs defs = defs {prtUODecls = shiftCtor <$> prtUODecls defs}
      where
        shiftCtor (DConstructor idx name)
          | name == criCtorTypeName && idx > criCtorIdx = DConstructor (idx - 1) name
        shiftCtor d = d

    updateMatchers defs = transformBi removeCase defs
    removeCase :: Term lang -> Term lang
    removeCase (SystF.App (SystF.Free (TermSig name)) args)
      | name == criDtorName = SystF.App (SystF.Free (TermSig name)) $ prefix <> removeAt criCtorIdx cases
      where
        (prefix, cases) = splitArgsTermsTail args
    removeCase t = t

removeAt :: Int -> [a] -> [a]
removeAt pos = uncurry (<>) . second (drop 1) . splitAt pos
