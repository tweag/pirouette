{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Collapse lambdas" #-}

-- | Constraints that we can translate to SMT
module Pirouette.SMT.Constraints where

import Control.Applicative
import Control.Monad
import Data.Default
import Data.Either
import qualified Data.Map as M
import qualified Data.Set as S
import Pirouette.Monad
import Pirouette.SMT.Base
import Pirouette.SMT.FromTerm
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT
import qualified UnionFind as UF

data ConstraintSet lang meta = ConstraintSet
  { -- | Represents the set of productive symbolic variable assignments we know
    -- of. Productive in the sense that we will always have at least one
    -- constructor on the rhs. The assignments are stored from /equivalence
    -- classes of symbolic variables/ to @TermMeta@.
    csAssignments :: UF.UnionFind meta (TermMeta lang meta),
    -- | Any potential native constraint we might need.
    csNative :: [PureSMT.SExpr],
    -- | And finally, pairs of terms we've discovered /not/ to be equal
    csRelations :: [(TermRelation, TermMeta lang meta, TermMeta lang meta)]
  }

-- instance (Ord meta, Semigroup meta) => Semigroup (ConstraintSet lang meta) where
--   s1 <> s2 =
--     ConstraintSet
--       (csAssignments s1 <> csAssignments s2)
--       (csNative s1 <> csNative s2)
--       (csRelations s1 <> csRelations s2)

-- instance (Ord meta) => Monoid (ConstraintSet lang meta) where
--   mempty = def

instance Default (ConstraintSet lang meta) where
  def = ConstraintSet UF.empty [] []

instance (LanguagePretty lang, Pretty meta) => Show (ConstraintSet lang meta) where
  show = show . pretty

instance (Pretty meta, Pretty (TermMeta lang meta)) => Pretty (ConstraintSet lang meta) where
  pretty ConstraintSet {..} = undefined
    -- vsep $
    --   [pretty csAssignments]
    --     ++ map prettyRelations csRelations
    --     ++ map prettyNative csNative
    -- where
    --   prettyRelations (r, v, u) = pretty v <+> pretty r <+> pretty u
    --   prettyNative n = pretty (show n)

instance Pretty TermRelation where
  pretty TREqual = "=="
  pretty TRNotEqual = "/="

-- | Calling @conjunct c cs@ will return @Nothing@ if the addition of @c@ into the 'ConstraintSet'
-- @cs@ makes it provably UNSAT. If @conjunct c cs == Just cs'@, there
-- is /no guarantee/ that @cs'@ is SAT, you must still validate it on a SMT solver.
--
-- WARNING: Do not pass constraints involving 'SystF.Lam' and 'SystF.Abs', these are not implemented
-- and we're not sure they even should be implemented.
conjunct ::
  forall lang meta.
  (Language lang, Pretty meta, Ord meta) =>
  Constraint lang meta ->
  ConstraintSet lang meta ->
  Maybe (ConstraintSet lang meta)
conjunct c cs0 =
  case c of
    -- TODO: Actually... we could be calling the smt solver right here to check that this
    -- sexpr is consistent with cs0, but let's leave that for later.
    Native sexpr -> Just $ cs0 {csNative = sexpr : csNative cs0}
    Unifiable t u -> unifyWith cs0 t u
    -- TODO: can we attempt to unify t and u below, when tr is TREqual, and, upon
    -- succeeding, producing a richer set of concstraints? Would that make sense?
    -- An argument against that is that on call sites, we should have information about whether
    -- we want to unify things: '=:=' or just register them as equal: 'termEq'
    Related tr t u -> Just $ cs0 {csRelations = (tr, t, u) : csRelations cs0}
  where
    -- TODO: The functions below feel like a dangerous re-implementation of union find.
    -- We should just rely on a library or implement this somewhere else and write a
    -- nice test suite so we can rely on it. For now, this will do, but this
    -- is of utmost priority!

    -- Looking up representatives of equivalence classes (in csMetaEq) should really
    -- be a single map lookup. Great first issue for a new pirouette developer! :)

    -- Attempts to unify two terms in an environment given by a current known set
    -- of constraints. Returns @Nothing@ when the terms can't be unified.
    unifyWith ::
      ConstraintSet lang meta ->
      TermMeta lang meta ->
      TermMeta lang meta ->
      Maybe (ConstraintSet lang meta)
    unifyWith cs (SystF.App (SystF.Meta v) []) u = unifyMetaWith cs v u
    unifyWith cs v (SystF.App (SystF.Meta u) []) = unifyMetaWith cs u v
    unifyWith cs (SystF.App hdT argsT) (SystF.App hdU argsU) = do
      guard (hdT == hdU)
      guard (length argsT == length argsU)
      iterateM cs $ zipWith (\x y -> \cs' -> unifyArgWith cs' x y) argsT argsU
      where
        iterateM :: (Monad m) => a -> [a -> m a] -> m a
        iterateM a [] = return a
        iterateM a (f : fs) = f a >>= flip iterateM fs
    unifyWith _ t u =
      error $
        "unifyWith: Unimplemented for:\n"
          ++ unlines (map (renderSingleLineStr . pretty) [t, u])

    -- Attempts to unify a metavariable with a term; will perform any potential lookup
    -- that is needed. WARNING: no occurs-check is performed, if the variable occurs within
    -- the term this function will loop. For our particular use case we don't need to occurs
    -- check since we'll only ever attempt to unify terms that have generated metavariables.
    unifyMetaWith ::
      ConstraintSet lang meta ->
      meta ->
      TermMeta lang meta ->
      Maybe (ConstraintSet lang meta)
    unifyMetaWith cs v u =
      -- FIXME: We are dropping the optimised union-find here, by using @snd@.
      case snd $ UF.lookup v (csAssignments cs) of
        -- @v@ is known to be a given term that has to be unfifiable with @u@
        Just (Just t) -> unifyWith cs t u
        -- @v@ is known but does not link to any value. FIXME: Therefore, it
        -- looks like we are violating an invariant of `unifyNewMetaWith`.
        Just Nothing -> Just $ unifyNewMetaWith cs v u
        -- @v@ is unknown, aka. /new/
        Nothing -> Just $ unifyNewMetaWith cs v u

    -- Like 'unifyMetaWith', but assumes that the 'meta' in question is not
    -- known by our current constraints.
    unifyNewMetaWith ::
      ConstraintSet lang meta ->
      meta ->
      TermMeta lang meta ->
      ConstraintSet lang meta
    unifyNewMetaWith cs v (SystF.App (SystF.Meta u) []) =
      cs { csAssignments = UF.trivialUnion v u (csAssignments cs) }
    unifyNewMetaWith cs v u =
      cs { csAssignments = UF.trivialInsert v u (csAssignments cs) }
    -- FIXME: The fact that we are only using trivial unions and insert probably
    -- means that we are still doing the job of the union-find. At least, we
    -- have it to back us up and check that these insertions and unions are
    -- indeed trivial. We should instead define what needs to happen when unions
    -- are non-trivial, and then we could get rid of the difference between
    -- `unifyMetaWith` and `unifyNewMetaWith`.

    unifyArgWith ::
      ConstraintSet lang meta ->
      ArgMeta lang meta ->
      ArgMeta lang meta ->
      Maybe (ConstraintSet lang meta)
    unifyArgWith cs (SystF.TermArg x) (SystF.TermArg y) = unifyWith cs x y
    unifyArgWith cs (SystF.TyArg _) (SystF.TyArg _) = Just cs -- TODO: unify types too? I don't think so
    unifyArgWith _ _ _ = Nothing

expandDefOf :: (Ord meta) => ConstraintSet lang meta -> meta -> Maybe (TermMeta lang meta)
expandDefOf cs v =
  -- FIXME: with @snd@, we forget the optimised version of the union-find structure.
  UF.join $ snd $ UF.lookup v (csAssignments cs)

-- | Since the translation of individual constraints can fail,
-- the translation of constraints does not always carry all the information it could.
-- So the boolean indicates if every atomic constraint have been translated.
-- A 'False' indicates that some have been forgotten during the translation.
constraintSetToSExpr ::
  forall lang meta m.
  (Ord meta, LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  S.Set Name ->
  ConstraintSet lang meta ->
  m (Bool, UsedAnyUFs, PureSMT.SExpr)
constraintSetToSExpr knownNames ConstraintSet {..} = do
  -- FIXME: this is dropping the optimised version of the union-find structure.
  let (_, metaEqList, assignmentsList) = UF.toLists csAssignments
  eAssignments <- mapM (runTranslator . uncurry trAssignment) assignmentsList
  eNotEq <- mapM (runTranslator . trRelations) csRelations
  let es = eAssignments ++ eNotEq
  let (trs, usedUFs) = unzip (rights es)
  let eEquivalences = map (uncurry trSymVarEq) metaEqList
  return (all isRight es, mconcat usedUFs, PureSMT.andMany (csNative ++ eEquivalences ++ trs))
  where
    trRelations :: (TermRelation, TermMeta lang meta, TermMeta lang meta) -> TranslatorT m PureSMT.SExpr
    trRelations (r, tx, ty) = do
      tx' <- translateTerm knownNames tx
      ty' <- translateTerm knownNames ty
      return $ trTermRelation r tx' ty'

    trTermRelation :: TermRelation -> PureSMT.SExpr -> PureSMT.SExpr -> PureSMT.SExpr
    trTermRelation TREqual a b = PureSMT.eq a b
    trTermRelation TRNotEqual a b = PureSMT.not (PureSMT.eq a b)

    trAssignment :: meta -> TermMeta lang meta -> TranslatorT m PureSMT.SExpr
    trAssignment name term = do
      let smtName = translate name
      d <- translateTerm knownNames term
      return $ smtName `PureSMT.eq` d

    trSymVarEq :: meta -> meta -> PureSMT.SExpr
    trSymVarEq a b =
      let aName = translate a
          bName = translate b
       in aName `PureSMT.eq` bName

-- * Single Constraint

-- | A 'Branch' is used to attach a number of atomic 'Constraint's to
--  a new term.
data Branch lang meta = Branch
  { additionalInfo :: [Constraint lang meta],
    newTerm :: TermMeta lang meta
  }

-- | Which relations between terms we support. Note that @TRUnifiable@ is different from @TREqual@.
-- Semantically, the 'Constraint' (in pseudo-syntax):
--
-- > Unifiable ($s1 - 1) 0
--
-- Will fail. That is, trying to 'conjunct' that constraint to a 'ConstraintSet' will return @Nothing@.
-- On the other hand, saying:
--
-- > Related TREqual ($s1 - 1) 0
--
-- succeeds, and produces a constraint set that records a new definitional equality: @s1 - 1@ /IS/ @0@.
data TermRelation = TREqual | TRNotEqual
  deriving (Eq, Show)

data Constraint lang meta
  = Related TermRelation (TermMeta lang meta) (TermMeta lang meta)
  | Unifiable (TermMeta lang meta) (TermMeta lang meta)
  | Native PureSMT.SExpr

instance (LanguagePretty lang, Pretty meta) => Pretty (Constraint lang meta) where
  pretty (Related tr x y) = pretty x <+> pretty tr <+> pretty y
  pretty (Unifiable x y) = pretty x <+> "~" <+> pretty y
  pretty (Native sexpr) = parens ("sexpr" <+> viaShow sexpr)

-- * Smart constructors

termEq :: TermMeta lang meta -> TermMeta lang meta -> Constraint lang meta
termEq = Related TREqual

termNotEq :: TermMeta lang meta -> TermMeta lang meta -> Constraint lang meta
termNotEq = Related TRNotEqual

native :: PureSMT.SExpr -> Constraint lang meta
native = Native

(=:=) :: meta -> TermMeta lang meta -> Constraint lang meta
a =:= t = Unifiable (SystF.App (SystF.Meta a) []) t

symVarEq :: meta -> meta -> Constraint lang meta
symVarEq x y = x =:= SystF.App (SystF.Meta y) []
