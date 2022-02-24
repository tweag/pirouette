{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Term.Syntax.Pretty (module Pirouette.Term.Syntax.Pretty.Class) where

import qualified Data.Map as Map
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.Pretty.Class
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Prettyprinter hiding (Pretty, pretty)

-- * SystemF Instances

instance Pretty SystF.Kind where
  prettyPrec _ SystF.KStar = "*"
  prettyPrec d (SystF.KTo t u) = parensIf (d > 10) (pp 11 t <+> "=>" <+> pp 10 u)

instance (Pretty meta, Pretty ann, Pretty f) => Pretty (SystF.VarMeta meta ann f) where
  pretty (SystF.Bound ann i) = pretty i <> "#" <> pretty ann
  pretty (SystF.Free f) = pretty f
  pretty (SystF.Meta m) = "$" <> pretty m

instance (Pretty ann, Pretty f) => Pretty (SystF.AnnType ann f) where
  prettyPrec d (SystF.TyApp n args) = prettyPrecApp d n args align
  prettyPrec d (SystF.TyFun t u) = parensIf (d > 11) (pp 12 t <+> "->" <+> pp 11 u)
  prettyPrec d t@SystF.TyLam {} = parensIf (d > 10) $ assoclBinder "λ" isTyLam d t
    where
      isTyLam (SystF.TyLam ann tx body) = Just (ann, tx, body)
      isTyLam _ = Nothing
  prettyPrec d t@SystF.TyAll {} = parensIf (d > 10) $ assoclBinder "∀" isTyLam d t
    where
      isTyLam (SystF.TyAll ann tx body) = Just (ann, tx, body)
      isTyLam _ = Nothing

instance (Pretty x) => Pretty (SystF.Ann x) where
  prettyPrec _ (SystF.Ann x) = pretty x

instance (Pretty ty, Pretty f) => Pretty (SystF.Arg ty f) where
  prettyPrec d (SystF.TermArg x) = prettyPrec d x
  prettyPrec d (SystF.TyArg x) = "@" <> prettyPrec 12 x

instance (Pretty ty, Pretty ann, Pretty f) => Pretty (SystF.AnnTerm ann ty f) where
  prettyPrec d (SystF.App n args) = prettyPrecApp d n args (nest 4)
  prettyPrec d t@SystF.Lam {} = parensIf (d > 11) $ assoclBinder "λ" isTyLam d t
    where
      isTyLam (SystF.Lam ann tx body) = Just (ann, tx, body)
      isTyLam _ = Nothing
  prettyPrec d t@SystF.Abs {} = parensIf (d > 10) $ assoclBinder "Λ" isTyLam d t
    where
      isTyLam (SystF.Abs ann tx body) = Just (ann, tx, body)
      isTyLam _ = Nothing

instance (PrettyLang builtins) => Pretty (FunDef builtins) where
  pretty (FunDef _ t ty) = align $ vsep [pretty ty, pretty t]

instance (PrettyLang builtins) => Pretty (Definition builtins) where
  pretty (DFunDef funDef) = pretty funDef
  pretty (DConstructor i ty) = "Constructor" <+> pretty i <+> pretty ty
  pretty (DDestructor ty) = "Destructor" <+> pretty ty
  pretty (DTypeDef ty) = "Type" <+> pretty ty

instance (Pretty (BuiltinTypes builtins)) => Pretty (TypeBase builtins) where
  pretty (TyBuiltin x) = pretty x
  pretty (TypeFromSignature n) = pretty n

instance
  (Pretty (BuiltinTerms builtins), Pretty (Constants builtins)) =>
  Pretty (TermBase builtins)
  where
  pretty (Constant x) = pretty x
  pretty (Builtin x) = "b/" <> pretty x
  pretty (TermFromSignature x) = pretty x
  pretty Bottom = "ERROR"

instance (Pretty (BuiltinTypes builtins)) => Pretty (TypeDef builtins) where
  pretty (Datatype k vars dest cs) =
    let pvars = sep (map (\(n, k) -> pretty n <> ":" <> pretty k) vars)
     in "data"
          <+> align
            ( vsep $
                [pvars, pretty dest]
                  ++ map (\(n, ty) -> pretty n <+> ":" <+> pretty ty) cs
            )

instance (PrettyLang builtins) => Pretty (Decls builtins) where
  pretty = align . vsep . map prettyDef . Map.toList
    where
      prettyDef (name, def) = pretty name <+> "|->" <+> pretty def
