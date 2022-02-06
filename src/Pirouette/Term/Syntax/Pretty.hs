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

import           Control.Arrow(first)
import qualified Data.ByteString           as BS
import qualified Data.Text                 as T
import qualified Prettyprinter as Prettyprint (Pretty, pretty)
import           Prettyprinter hiding (Pretty, pretty)
import           Prettyprinter.Render.Text
import Data.Void

instance Pretty Void where
  pretty = absurd

instance Pretty Integer where
  pretty = Prettyprint.pretty

instance Pretty Int where
  pretty = Prettyprint.pretty

instance Pretty Char where
  pretty = Prettyprint.pretty

instance Pretty T.Text where
  pretty = Prettyprint.pretty

instance Pretty Bool where
  pretty = Prettyprint.pretty

instance Pretty BS.ByteString where
  pretty = prettyList . BS.unpack

instance (Pretty a, Pretty b) => Pretty (a , b) where
  prettyPrec d (x , y) = parens $ prettyPrec 10 x <+> comma <+> prettyPrec 10 y

instance {-# OVERLAPPING #-} Pretty String where
  pretty = Prettyprint.pretty

instance {-# OVERLAPPABLE #-} (Pretty a) => Pretty [a] where
  prettyPrec d = brackets . align . sep . punctuate comma . map pretty

-- * SystemF Instances

instance Pretty SF.Kind where
  prettyPrec _ SF.KStar     = "*"
  prettyPrec d (SF.KTo t u) = parensIf (d > 10) (pp 11 t <+> "=>" <+> pp 10 u )

instance (Pretty meta, Pretty ann, Pretty f) => Pretty (SF.VarMeta meta ann f) where
  pretty (SF.B ann i) = pretty i <> "#" <> pretty ann
  pretty (SF.F f)     = pretty f
  pretty (SF.M m)     = "$" <> pretty m

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
  prettyPrec d (SF.Arg   x) = prettyPrec d x
  prettyPrec d (SF.TyArg x) = "@" <> prettyPrec 12 x

instance (Pretty ty, Pretty ann, Pretty f) => Pretty (SF.AnnTerm ann ty f) where
  prettyPrec d (SF.App n args) = prettyPrecApp d n args (nest 4)
  prettyPrec d t@SF.Lam{} = parensIf (d > 11) $ assoclBinder "λ" isTyLam d t
    where isTyLam (SF.Lam ann tx body) = Just (ann, tx, body)
          isTyLam _                    = Nothing
  prettyPrec d t@SF.Abs{} = parensIf (d > 10) $ assoclBinder "Λ" isTyLam d t
    where isTyLam (SF.Abs ann tx body) = Just (ann, tx, body)
          isTyLam _                    = Nothing

instance (Pretty name, Pretty (BuiltinTypes lang), Pretty (BuiltinTerms lang), Pretty (Constants lang))
    => Pretty (Definition lang name) where
  pretty (DFunction _ t ty)  = align $ vsep [pretty ty, pretty t]
  pretty (DConstructor i ty) = "Constructor" <+> pretty i <+> pretty ty
  pretty (DDestructor ty)    = "Destructor" <+> pretty ty
  pretty (DTypeDef ty)       = "Type" <+> pretty ty

instance (Pretty name, Pretty (BuiltinTypes lang)) => Pretty (TypeBase lang name) where
  pretty (TyBuiltin x)   = pretty x
  pretty (TyFree n)      = pretty n

instance (Pretty name, Pretty (BuiltinTerms lang), Pretty (Constants lang))
    => Pretty (TermBase lang name) where
  pretty (Constant x)   = pretty x
  pretty (Builtin x)    = "b/" <> pretty x
  pretty (FreeName x)   = pretty x
  pretty Bottom         = "error"

instance (Pretty name, Pretty (BuiltinTypes lang)) => Pretty (TypeDef lang name) where
  pretty (Datatype k vars dest cs) =
    let pvars = sep (map (\(n, k) -> pretty n <> ":" <> pretty k) vars)
     in "data" <+> align (vsep $ [pvars, pretty dest]
                              ++ map (\(n , ty) -> pretty n <+> ":" <+> pretty ty) cs)
