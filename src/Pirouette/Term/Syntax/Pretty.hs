{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Pirouette.Term.Syntax.Pretty where

import qualified Pirouette.Term.Syntax.SystemF as SF
import           Pirouette.Term.Syntax.Base

import           Control.Arrow(first)
import qualified Data.ByteString           as BS
import qualified Data.Text                 as T
import qualified Data.Text.Prettyprint.Doc as Prettyprint (Pretty, pretty)
import           Data.Text.Prettyprint.Doc hiding (Pretty, pretty)
import           Data.Text.Prettyprint.Doc.Render.Text

-- |Renders a doc in a single line.
renderSingleLine :: Doc ann -> T.Text
renderSingleLine = renderStrict . layoutPretty (LayoutOptions Unbounded)

-- |Rendes a doc in a smart fashion in a large line.
renderSmart :: Doc ann -> T.Text
renderSmart = renderStrict . layoutSmart (LayoutOptions (AvailablePerLine 100 1))

renderSingleLineStr :: Doc ann -> String
renderSingleLineStr = T.unpack . renderSingleLine

class Pretty x where
  -- |Just like 'showsPrec', it receives the precedence of the encloding context.
  -- Unlike 'showsPrec', this just returns a 'Doc' and we hope the underlying
  -- library has efficient concatenation of docs.
  --
  -- Good rule of thumb for dealing with infix associative operators:
  --
  -- * infix n: use @parensIf (p > n)@, @prettyPrec (n+1)@ on the left, and @prettyPrec (n+1)@ on the right
  -- * infixl n: use @parensIf (p > n)@, @prettyPrec n@ on the left, and @prettyPrec (n+1)@ on the right
  -- * infixr n: dual to the infixl case.
  -- * non-infix: use @parensIf (p > 10)@ and @prettyPrec 11@ on the arguments
  prettyPrec :: Int -> x -> Doc ann

  pretty :: x -> Doc ann
  pretty = prettyPrec 0

  prettyPrec _ = pretty

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

pp :: (Pretty x) => Int -> x -> Doc ann
pp = prettyPrec

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  = parens
parensIf False = id

-- * SystemF Instances

instance Pretty SF.Kind where
  prettyPrec _ SF.KStar     = "*"
  prettyPrec d (SF.KTo t u) = parensIf (d > 10) (pp 11 t <+> "=>" <+> pp 10 u )

instance (Pretty ann, Pretty f) => Pretty (SF.Var ann f) where
  pretty (SF.B ann i) = pretty i <> "#" <> pretty ann
  pretty (SF.F f)     = pretty f

assoclBinder :: forall dann ann ty body
              . (Pretty ann, Pretty ty, Pretty body)
             => Doc dann
             -> (body -> Maybe (ann, ty, body))
             -> Int -> body -> Doc dann
assoclBinder binder f d x = case go x of
  (ns, b) -> let parens = parensIf (length ns > 1)
              in parensIf (d > 10) $ align $ fillSep
               [ binder
               , align (fillSep $ map (\(ann, ty) -> parens $ pretty ann <+> ":" <+> pretty ty) ns)
               , "." <+> pretty b
               ]
 where
   go :: body -> ([(ann, ty)], body)
   go b = case f b of
     Nothing            -> ([], b)
     Just (ann, ty, b') -> first ((ann, ty):) $ go b'

prettyPrecApp :: (Pretty n , Pretty arg) => Int -> n -> [arg] -> (Doc ann -> Doc ann) -> Doc ann
prettyPrecApp _ n []   al = pretty n
prettyPrecApp d n args al = parensIf (d > 10) $ pretty n <+> al (sep $ map (prettyPrec 11) args)

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

-- * Plutus-specific Instances

instance Pretty PIRType where
  pretty PIRTypeInteger    = "Integer"
  pretty PIRTypeByteString = "ByteString"
  pretty PIRTypeUnit       = "Unit"
  pretty PIRTypeBool       = "Bool"
  pretty PIRTypeString     = "String"
  pretty (PIRTypeList a)   = brackets (sep ["List", pretty a])
  pretty (PIRTypePair a b) = brackets (sep ["Pair", pretty a, pretty b])

instance (Pretty tyname) => Pretty (TypeBase tyname) where
  pretty (TyBuiltin x)   = pretty x
  pretty (TyFree n)      = pretty n

instance (Pretty n) => Pretty (TypeDef n) where
  pretty (Datatype k vars dest cs) =
    let pvars = sep (map (\(n, k) -> pretty n <> ":" <> pretty k) vars)
     in "data" <+> align (vsep $ [pvars, pretty dest]
                              ++ map (\(n , ty) -> pretty n <+> ":" <+> pretty ty) cs)

instance Pretty PIRConstant where
  pretty (PIRConstInteger x) = pretty x
  pretty (PIRConstByteString x) = "b" <> pretty x
  pretty PIRConstUnit = "unit"
  pretty (PIRConstBool x) = pretty x
  pretty (PIRConstString x) = dquotes (pretty x)
  pretty (PIRConstList xs) = "l" <> brackets (sep $ punctuate comma $ map pretty xs)
  pretty (PIRConstPair x y) = "p" <> brackets (sep $ punctuate comma $ map pretty [x, y])

instance (Pretty fun, Pretty n) => Pretty (PIRBase fun n) where
  pretty (Constant x)   = pretty x
  pretty (Builtin x)    = "b/" <> pretty x
  pretty (FreeName x)   = pretty x
  pretty Bottom         = "error"

instance (Pretty name, Pretty fun) => Pretty (Definition name fun) where
  pretty (DFunction _ t ty)  = align $ vsep [pretty ty, pretty t]
  pretty (DConstructor i ty) = "Constructor" <+> pretty i <+> pretty ty
  pretty (DDestructor ty)    = "Destructor" <+> pretty ty
  pretty (DTypeDef ty)       = "Type" <+> pretty ty
