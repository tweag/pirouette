{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Term.Syntax.Pretty
  (module Pirouette.Term.Syntax.Pretty.Class) where

import qualified Pirouette.Term.Syntax.SystemF as SF
import           Pirouette.Term.Syntax.Base
import           Pirouette.Term.Syntax.Pretty.Class

import           Prettyprinter hiding (Pretty, pretty)

-- * SystemF Instances

instance Pretty SF.Kind where
  prettyPrec _ SF.KStar     = "*"
  prettyPrec d (SF.KTo t u) = parensIf (d > 10) (pp 11 t <+> "=>" <+> pp 10 u )

instance (Pretty meta, Pretty ann, Pretty f) => Pretty (SF.VarMeta meta ann f) where
  pretty (SF.Bound ann i) = pretty i <> "#" <> pretty ann
  pretty (SF.Free f)     = pretty f
  pretty (SF.Meta m)     = "$" <> pretty m

instance (Pretty ann, Pretty f) => Pretty (SF.AnnType ann f) where
  prettyPrec d (SF.TyApp n args) = prettyPrecApp d n args align
  prettyPrec d (SF.TyFun t u) = parensIf (d > 11) (pp 12 t <+> "->" <+> pp 11 u )
  prettyPrec d t@SF.TyLam{} = parensIf (d > 10) $ assoclBinder "λ" isTyLam d t
    where isTyLam (SF.TyLam ann tx body) = Just (ann, tx, body)
          isTyLam _                      = Nothing
  prettyPrec d t@SF.TyAll{} = parensIf (d > 10) $ assoclBinder "∀" isTyLam d t
    where isTyLam (SF.TyAll ann tx body) = Just (ann, tx, body)
          isTyLam _                      = Nothing

instance (Pretty x) => Pretty (SF.Ann x) where
  prettyPrec _ (SF.Ann x) = pretty x

instance (Pretty ty, Pretty f) => Pretty (SF.Arg ty f) where
  prettyPrec d (SF.TermArg   x) = prettyPrec d x
  prettyPrec d (SF.TyArg x) = "@" <> prettyPrec 12 x

instance (Pretty ty, Pretty ann, Pretty f) => Pretty (SF.AnnTerm ann ty f) where
  prettyPrec d (SF.App n args) = prettyPrecApp d n args (nest 4)
  prettyPrec d t@SF.Lam{} = parensIf (d > 11) $ assoclBinder "λ" isTyLam d t
    where isTyLam (SF.Lam ann tx body) = Just (ann, tx, body)
          isTyLam _                    = Nothing
  prettyPrec d t@SF.Abs{} = parensIf (d > 10) $ assoclBinder "Λ" isTyLam d t
    where isTyLam (SF.Abs ann tx body) = Just (ann, tx, body)
          isTyLam _                    = Nothing

instance (Pretty (BuiltinTypes lang), Pretty (BuiltinTerms lang), Pretty (Constants lang))
    => Pretty (Definition lang) where
  pretty (DFunction _ t ty)  = align $ vsep [pretty ty, pretty t]
  pretty (DConstructor i ty) = "Constructor" <+> pretty i <+> pretty ty
  pretty (DDestructor ty)    = "Destructor" <+> pretty ty
  pretty (DTypeDef ty)       = "Type" <+> pretty ty

instance (Pretty (BuiltinTypes lang)) => Pretty (TypeBase lang) where
  pretty (TyBuiltin x)   = pretty x
  pretty (TypeFromSignature n)      = pretty n

instance (Pretty (BuiltinTerms lang), Pretty (Constants lang))
    => Pretty (TermBase lang) where
  pretty (Constant x)   = pretty x
  pretty (Builtin x)    = "b/" <> pretty x
  pretty (TermFromSignature x)   = pretty x

instance (Pretty (BuiltinTypes lang)) => Pretty (TypeDef lang) where
  pretty (Datatype k vars dest cs) =
    let pvars = sep (map (\(n, k) -> pretty n <> ":" <> pretty k) vars)
     in "data" <+> align (vsep $ [pvars, pretty dest]
                              ++ map (\(n , ty) -> pretty n <+> ":" <+> pretty ty) cs)
