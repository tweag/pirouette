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

import Control.Monad
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer.Strict (WriterT, tell)
import Data.Default
import Data.Either
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as S
import Pirouette.Monad
import Pirouette.SMT.Base
import Pirouette.SMT.FromTerm
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT
import qualified UnionFind as UF
import qualified UnionFind.Action as UF
import qualified UnionFind.Deferring as UF

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

instance Default (ConstraintSet lang meta) where
  def = ConstraintSet UF.empty [] []

instance (Ord meta, LanguagePretty lang, Pretty meta) => Show (ConstraintSet lang meta) where
  show = show . pretty

instance (Ord meta, Pretty meta, Pretty (TermMeta lang meta)) => Pretty (ConstraintSet lang meta) where
  pretty ConstraintSet {..} =
    let unionFindL = fst $ UF.runWithUnionFind csAssignments UF.toList
     in vsep $
          map (uncurry prettyEqClassAndValue) unionFindL
            ++ map prettyRelations csRelations
            ++ map prettyNative csNative
    where
      prettyEqClassAndValue eqClass Nothing =
        prettyEqClass eqClass
      prettyEqClassAndValue eqClass (Just value) =
        prettyEqClass eqClass <+> ":=" <+> pretty value
      prettyEqClass eqClass =
        foldl
          (\p key -> p <+> "~~" <+> pretty key)
          (pretty (NonEmpty.head eqClass))
          (NonEmpty.tail eqClass)
      prettyRelations (r, v, u) = pretty v <+> pretty r <+> pretty u
      prettyNative n = pretty (show n)

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
    -- Takes a constraint set and two terms and attempts to unify the two
    -- terms, adding new constraints along the way. Returns @Nothing@ when the
    -- unification is impossible.
    unifyWith ::
      ConstraintSet lang meta ->
      TermMeta lang meta ->
      TermMeta lang meta ->
      Maybe (ConstraintSet lang meta)
    unifyWith cs v u = do
      -- The logic is in @unificationActions@ which yields a list of union-find
      -- actions (either 'union' or 'insert') on meta-variables in the terms.
      -- The following piece of code simply gets those actions and runs them in
      -- the @csAssignments@ union-find structure. This might trigger new
      -- actions, hence the use of 'applyActionsWithDeferring'.
      actions <- unificationActions v u
      assignments <-
        UF.execWithUnionFindT (csAssignments cs) $
          UF.applyActionsWithDeferring merge actions
      Just $ cs {csAssignments = assignments}
      where
        merge ::
          TermMeta lang meta ->
          TermMeta lang meta ->
          WriterT [UF.Action meta (TermMeta lang meta)] Maybe (TermMeta lang meta)
        merge v' u' = do
          actions <- lift $ unificationActions v' u'
          tell actions
          return v'

    -- Takes two terms and returns a list of union/insert actions that would
    -- be necessary to unify the two terms, or @Nothing@ if it is impossible.
    unificationActions ::
      TermMeta lang meta ->
      TermMeta lang meta ->
      Maybe [UF.Action meta (TermMeta lang meta)]
    unificationActions (SystF.App (SystF.Meta t) []) (SystF.App (SystF.Meta u) []) = Just [UF.Union t u]
    unificationActions (SystF.App (SystF.Meta t) []) u = Just [UF.Insert t u]
    unificationActions t (SystF.App (SystF.Meta u) []) = Just [UF.Insert u t]
    unificationActions (SystF.App hdT argsT) (SystF.App hdU argsU) = do
      -- FIXME: Why must the heads be equal; shouldn't we unify them instead? I
      -- suppose there is a reason, eg. we know we are in weak normal form.
      guard (hdT == hdU)
      guard (length argsT == length argsU)
      concat <$> zipWithM unificationActions' argsT argsU
    unificationActions t u =
      error $
        "unifyWith: Unimplemented for:\n"
          ++ unlines (map (renderSingleLineStr . pretty) [t, u])

    -- Same as @unificationActions@ but for term application arguments.
    unificationActions' ::
      ArgMeta lang meta ->
      ArgMeta lang meta ->
      Maybe [UF.Action meta (TermMeta lang meta)]
    unificationActions' (SystF.TermArg t) (SystF.TermArg u) = unificationActions t u
    unificationActions' (SystF.TyArg _) (SystF.TyArg _) = Just [] -- TODO: unify types too? I don't think so
    unificationActions' _ _ = Nothing

expandDefOf :: (Ord meta) => ConstraintSet lang meta -> meta -> Maybe (TermMeta lang meta)
expandDefOf cs v =
  -- FIXME: with @snd@, we forget the optimised version of the @ConstraintSet@.
  UF.evalWithUnionFind (csAssignments cs) $ UF.lookup v

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
  let (metaEqList, assignmentsList) = fst $ UF.runWithUnionFind csAssignments UF.toLists
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
