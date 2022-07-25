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

-- @Arg Kind (Type lang)@ could've been used here instead,
-- but having a distinct type seems to be a bit nicer, at least for now for hole-driven development reasons.
data FlatArgType lang
  = FlatTyArg (Ann Name) Kind
  | FlatTermArg (Type lang)
  deriving (Show)

flattenType :: Type lang -> ([FlatArgType lang], Type lang)
flattenType ty@TyApp {} = ([], ty)
flattenType (dom `TyFun` cod) = first (FlatTermArg dom :) $ flattenType cod
flattenType (TyAll a k ty) = first (FlatTyArg a k :) $ flattenType ty
flattenType TyLam {} = error "unnormalized type"

unflattenType :: [FlatArgType lang] -> Type lang -> Type lang
unflattenType = flip $ foldr f
  where
    f (FlatTermArg dom) cod = dom `TyFun` cod
    f (FlatTyArg a k) ty = TyAll a k ty

-- | Splits a list of arguments into two lists:
-- the first one containing all arguments up to and including the last type argument,
-- and the second one containing the rest of the (term) arguments.
--
-- For example, on 'foo @ty1 term1 @ty2 term2 term3' it returns
-- '([@ty1, term1, @ty2], [term2, term3])'.
splitArgsTermsTail :: [SystF.Arg ty v] -> ([SystF.Arg ty v], [SystF.Arg ty v])
splitArgsTermsTail = swap . (reverse *** reverse) . span SystF.isArg . reverse
