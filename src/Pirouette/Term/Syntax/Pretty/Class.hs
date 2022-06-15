{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.Syntax.Pretty.Class where

import Control.Arrow (first)
import Data.ByteString as ByteString (ByteString, unpack)
import Data.Text as Text (Text, unpack)
import Data.Void
import Prettyprinter hiding (Pretty, pretty)
import qualified Prettyprinter as Prettyprint (pretty)
import Prettyprinter.Render.Text
import PureSMT.SExpr

-- | Renders a doc in a single line.
renderSingleLine :: Doc ann -> Text
renderSingleLine = renderStrict . layoutPretty (LayoutOptions Unbounded)

-- | Rendes a doc in a smart fashion in a large line.
renderSmart :: Doc ann -> Text
renderSmart = renderStrict . layoutSmart (LayoutOptions (AvailablePerLine 100 1))

renderSingleLineStr :: Doc ann -> String
renderSingleLineStr = Text.unpack . renderSingleLine

class Pretty x where
  -- | Just like 'showsPrec', it receives the precedence of the enclosing context.
  --  Unlike 'showsPrec', this just returns a 'Doc' and we hope the underlying
  --  library has efficient concatenation of docs.
  --
  --  Good rule of thumb for dealing with infix associative operators:
  --
  --  * infix n: use @parensIf (p > n)@, @prettyPrec (n+1)@ on the left, and @prettyPrec (n+1)@ on the right
  --  * infixl n: use @parensIf (p > n)@, @prettyPrec n@ on the left, and @prettyPrec (n+1)@ on the right
  --  * infixr n: dual to the infixl case.
  --  * non-infix: use @parensIf (p > 10)@ and @prettyPrec 11@ on the arguments
  prettyPrec :: Int -> x -> Doc ann

  pretty :: x -> Doc ann
  pretty = prettyPrec 0

  prettyPrec _ = pretty

prettyPrecApp :: (Pretty n, Pretty arg) => Int -> n -> [arg] -> (Doc ann -> Doc ann) -> Doc ann
prettyPrecApp _ n [] _ = pretty n
prettyPrecApp d n args al = parensIf (d > 10) $ pretty n <+> al (sep $ map (prettyPrec 11) args)

assoclBinder ::
  forall dann ann ty body.
  (Pretty ann, Pretty ty, Pretty body) =>
  Doc dann ->
  (body -> Maybe (ann, ty, body)) ->
  Int ->
  body ->
  Doc dann
assoclBinder binder f d x = case go x of
  (ns, b) ->
    let parens1 = parensIf (length ns > 1)
     in parensIf (d > 10) $
          align $
            fillSep
              [ binder,
                align (fillSep $ map (\(ann, ty) -> parens1 $ pretty ann <+> ":" <+> pretty ty) ns),
                "." <+> pretty b
              ]
  where
    go :: body -> ([(ann, ty)], body)
    go b = case f b of
      Nothing -> ([], b)
      Just (ann, ty, b') -> first ((ann, ty) :) $ go b'

pp :: (Pretty x) => Int -> x -> Doc ann
pp = prettyPrec

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True = parens
parensIf False = id

instance Pretty Void where
  pretty = absurd

instance Pretty Integer where
  pretty = Prettyprint.pretty

instance Pretty Int where
  pretty = Prettyprint.pretty

instance Pretty Char where
  pretty = Prettyprint.pretty

instance Pretty Text.Text where
  pretty = Prettyprint.pretty

instance Pretty Bool where
  pretty = Prettyprint.pretty

instance Pretty Float where
  pretty = Prettyprint.pretty

instance Pretty Double where
  pretty = Prettyprint.pretty

instance Pretty Rational where
  pretty x = Prettyprint.pretty (fromRational x :: Double)

instance Pretty ByteString where
  pretty = prettyList . ByteString.unpack

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  prettyPrec _ (Left x) = "Left" <+> prettyPrec 10 x
  prettyPrec _ (Right x) = "Right" <+> prettyPrec 10 x

instance (Pretty a, Pretty b) => Pretty (a, b) where
  prettyPrec _ (x, y) = parens $ prettyPrec 10 x <+> comma <+> prettyPrec 10 y

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  prettyPrec _ (x, y, z) = parens $ prettyPrec 10 x <+> comma <+> prettyPrec 10 y <+> comma <+> prettyPrec 10 z

instance {-# OVERLAPPING #-} Pretty String where
  pretty = Prettyprint.pretty

instance {-# OVERLAPPABLE #-} (Pretty a) => Pretty [a] where
  prettyPrec _ = brackets . align . sep . punctuate comma . map pretty

instance Pretty ShowS where
  pretty = pretty . ($ "")

instance Pretty Value where
  pretty (Bool b) = pretty b
  pretty (Int n) = pretty n
  pretty (Real r) = pretty r
  pretty (Bits _n v) = "#x" <> pretty v
  pretty (Other e) = pretty e

instance Pretty SExpr where
  pretty p = pretty $ showsSExprHaskellish p
