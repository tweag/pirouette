{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.DCE where

import Control.Arrow (second)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Generics.Uniplate.Data
import Data.List (isPrefixOf)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils
import Pirouette.Utils

removeDeadCtors :: forall lang. (Language lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
removeDeadCtors = undefined

findDeadCtors :: forall lang. (Language lang) => PrtUnorderedDefs lang -> [CtorRemoveInfo]
findDeadCtors = undefined

data CtorRemoveInfo = CtorRemoveInfo
  { criDtorName :: Name
  , criCtorIdx :: Int
  , criCtorTypeName :: Name
  }

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
