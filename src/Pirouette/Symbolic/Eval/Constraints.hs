{-# HLINT ignore "Collapse lambdas" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Pirouette.Symbolic.Eval.Constraints where

import Control.Arrow ((&&&))
import Control.Monad
import Data.Default
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Tuple (swap)
import Pirouette.Monad
import Pirouette.SMT.Base
import Pirouette.SMT.FromTerm
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT

data Constraints lang meta = Constraints
  { -- | Represents the set of productive symbolic variable assignments we know of.
    -- Productive in the sense that we will always have at least one constructor
    -- on the rhs.
    csAssignments :: M.Map meta (TermMeta lang meta),
    -- | Represents the symbolic variable equivalences we know of. Satisfies the invariant
    -- that if @M.lookup v csmetaEq == Just v'@, then @v' < v@ (lexicographically)
    csMetaEq :: M.Map meta meta,
    -- | And any potential native constraint we might need.
    csNative :: [PureSMT.SExpr]
  }

-- | TODO: If is often the case that we will start seeing constraints that look like:
--
--  > s0 := Suc $s2
--  > s1 := Suc $s2
--  > s2 := Zero
--
--  Whereas what we actually wanted is something like:
--
--  > s0 := Suc Zero
--  > s1 ~~ s0
--  > s2 ~~ s0
--
--  Which encodes the very same information and would give a much more meaningful
compress :: (Ord meta, LanguageBuiltins lang) => Constraints lang meta -> Constraints lang meta
compress Constraints {..} = undefined

-- let invLkup = M.fromListWith S.union $ map (snd &&& S.singleton . fst) $ M.toList csAssignments
--  in _

instance (Ord meta) => Semigroup (Constraints lang meta) where
  s1 <> s2 =
    Constraints
      (csAssignments s1 <> csAssignments s2)
      (csMetaEq s1 <> csMetaEq s2)
      (csNative s1 <> csNative s2)

instance (Ord meta) => Monoid (Constraints lang meta) where
  mempty = def

instance Default (Constraints lang meta) where
  def = Constraints M.empty M.empty []

instance (LanguagePretty lang, Pretty meta) => Pretty (Constraints lang meta) where
  pretty Constraints {..} =
    vsep $
      map (uncurry prettyAssignment) (M.toList csAssignments)
        ++ map (uncurry prettyMetaEq) (M.toList csMetaEq)
        ++ map prettyNative csNative
    where
      prettyAssignment v t = pretty v <+> pretty ":=" <+> pretty t
      prettyMetaEq v u = pretty v <+> pretty "~~" <+> pretty u
      prettyNative n = pretty (show n)

-- | Attempts to unify two terms in an environment given by a current known set
--  of constraints. Returns @Nothing@ when the terms can't be unified.
unifyWith ::
  (Pretty meta, Ord meta, Language lang) =>
  Constraints lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  Maybe (Constraints lang meta)
unifyWith cs (SystF.App (SystF.Meta v) []) u = unifyMetaWith cs v u
unifyWith cs v (SystF.App (SystF.Meta u) []) = unifyMetaWith cs u v
unifyWith cs (SystF.App hdT argsT) (SystF.App hdU argsU) = do
  guard (hdT == hdU)
  iterateM cs $ zipWith (\x y -> \cs' -> unifyArgWith cs' x y) argsT argsU
  where
    iterateM :: (Monad m) => a -> [a -> m a] -> m a
    iterateM a [] = return a
    iterateM a (f : fs) = f a >>= flip iterateM fs
unifyWith _ t u =
  error $
    "unifyWith:\n"
      ++ unlines (map (renderSingleLineStr . pretty) [t, u])

-- | Attempts to unify a metavariable with a term; will perform any potential lookup
--  that is needed. WARNING: no occurs-check is performed, if the variable occurs within
--  the term this function will loop. For our particular use case we don't need to occurs
--  check since we'll only ever attempt to unify terms that have generated metavariables.
unifyMetaWith ::
  (Pretty meta, Ord meta, Language lang) =>
  Constraints lang meta ->
  meta ->
  TermMeta lang meta ->
  Maybe (Constraints lang meta)
unifyMetaWith cs v u
  -- First we check whether @v@ is actually equal to anything else
  | Just t <- M.lookup v (csAssignments cs) = unifyWith cs t u
  -- If not, we check whether v is equivalent to some other smaller metavariable
  | Just v' <- M.lookup v (csMetaEq cs) = unifyMetaWith cs v' u
  | otherwise = Just $ unifyNewMetaWith cs v u

-- | Like 'unifyMetaWith', but assumes that the 'meta' in question is not
--  known by our current constraints.
unifyNewMetaWith ::
  (Pretty meta, Ord meta, Language lang) =>
  Constraints lang meta ->
  meta ->
  TermMeta lang meta ->
  Constraints lang meta
unifyNewMetaWith cs@Constraints {..} v (SystF.App (SystF.Meta u) [])
  | v == u = cs
  | Just t <- M.lookup u csAssignments = cs {csAssignments = M.insert v t csAssignments}
  | Just u' <- M.lookup u csMetaEq = unifyNewMetaWith cs v (SystF.App (SystF.Meta u') [])
  | otherwise = cs {csMetaEq = M.insert (max v u) (min v u) csMetaEq}
unifyNewMetaWith cs v u =
  cs {csAssignments = M.insert v u (csAssignments cs)}

unifyArgWith ::
  (Pretty meta, Ord meta, Language lang) =>
  Constraints lang meta ->
  ArgMeta lang meta ->
  ArgMeta lang meta ->
  Maybe (Constraints lang meta)
unifyArgWith cs (SystF.TermArg x) (SystF.TermArg y) = unifyWith cs x y
unifyArgWith cs (SystF.TyArg _) (SystF.TyArg _) = Just cs -- TODO: unify types too? I don't think so
unifyArgWith _ _ _ = Nothing

-- * Translating to SMT

constraintsToSExpr ::
  (LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  S.Set Name ->
  Constraints lang meta ->
  TranslatorT m PureSMT.SExpr
constraintsToSExpr = undefined
