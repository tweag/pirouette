{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

-- | Adapted from [S. Weirich lecture](https://www.cis.upenn.edu/~plclub/blog/2020-06-26-Strongly-typed-System-F/)
module Pirouette.Term.Syntax.Subst where

import Control.Monad.Identity
import Data.Maybe (fromMaybe)
import GHC.Stack (HasCallStack)

class IsVar v where
  type VarAnn v :: *

  isBound :: v -> Maybe Integer

  varMapM :: (Monad m) => (Integer -> m Integer) -> v -> m v

  varMap :: (Integer -> Integer) -> v -> v
  varMap f = runIdentity . varMapM (return . f)

  annMap :: (VarAnn v -> VarAnn v) -> v -> v

  varDec :: v -> v
  varDec = varMap (\x -> x - 1)

-- A substitution (represented by a datatype).
data Sub term
  = Inc Integer -- increment by an index amount.
  | Maybe term :< Sub term -- Explicitely define the image of the variable of index 0,
  -- followed by the substitution to applied to the other variables.
  -- This defines substitution as list of image, so `:<` is like cons. Nothing means Identity.
  | Sub term :<> Sub term -- compose substitutions.
  -- It must be noted that the chosen convention is the converse of the standard composition one.
  -- `s1 :<> s2` means "`s2` applied after `s1`"
  deriving (Eq, Show, Functor)

infixr 9 :< -- like usual cons operator (:)

infixr 9 :<> -- like usual composition (;)

--  Value of the index x in the substitution
applySub :: (HasSubst term) => Sub term -> SubstVar term -> term
applySub (ty :< s) x = case isBound x of
  Just 0 -> fromMaybe (var x) ty
  _ -> applySub s (varDec x)
applySub (Inc k) x = var $ varMap (k +) x
applySub (s1 :<> s2) x = subst s2 (applySub s1 x)

-- | Substitute `var 0` by t, leaving the rest alone.
singleSub :: term -> Sub term
singleSub t = Just t :< Inc 0

-- | General class for terms that support substitution
class (IsVar (SubstVar term)) => HasSubst term where
  type SubstVar term :: *

  -- | How to construct an annotatd bound variable
  var :: HasCallStack => SubstVar term -> term

  -- | How to apply a substitution
  subst :: HasCallStack => Sub term -> term -> term

-- |Shift all bound variables from @from@ by @k@
shiftFrom :: (HasSubst term) => Integer -> Integer -> term -> term
shiftFrom from k = subst $ foldr (\_ r -> Nothing :< r) (Inc k) [0 .. from - 1]

-- |Shift all bound variables by @k@
shift :: (HasSubst term) => Integer -> term -> term
shift = shiftFrom 0

-- | When traversing a binder, we want to leave Used in substitution when going under a binder
liftSub :: Sub termv -> Sub termv
liftSub s = Nothing :< (s :<> Inc 1)
