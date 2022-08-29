{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Constraints that we can translate to SMT
module Pirouette.SMT.Constraints where

import Control.Applicative
import Control.Monad
import Data.Default
import Data.Either
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Pirouette.Monad
import Pirouette.SMT.Base
import Pirouette.SMT.FromTerm
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT

data ConstraintSet lang meta = ConstraintSet
  { -- | Represents the set of productive symbolic variable assignments we know of.
    -- Productive in the sense that we will always have at least one constructor
    -- on the rhs.
    csAssignments :: M.Map meta (TermMeta lang meta),
    -- | Represents the symbolic variable equivalences we know of. Satisfies the invariant
    -- that if @M.lookup v csmetaEq == Just v'@, then @v' < v@ (lexicographically)
    csMetaEq :: M.Map meta meta,
    -- | Any potential native constraint we might need.
    csNative :: [PureSMT.SExpr],
    -- | And finally, pairs of terms we've discovered /not/ to be equal
    csNotEq :: [(TermMeta lang meta, TermMeta lang meta)]
  }

instance (Ord meta) => Semigroup (ConstraintSet lang meta) where
  s1 <> s2 =
    ConstraintSet
      (csAssignments s1 <> csAssignments s2)
      (csMetaEq s1 <> csMetaEq s2)
      (csNative s1 <> csNative s2)
      (csNotEq s1 <> csNotEq s2)

instance (Ord meta) => Monoid (ConstraintSet lang meta) where
  mempty = def

instance Default (ConstraintSet lang meta) where
  def = ConstraintSet M.empty M.empty [] []

instance (LanguagePretty lang, Pretty meta) => Show (ConstraintSet lang meta) where
  show = show . pretty

instance (LanguagePretty lang, Pretty meta) => Pretty (ConstraintSet lang meta) where
  pretty ConstraintSet {..} =
    vsep $
      map (uncurry prettyAssignment) (M.toList csAssignments)
        ++ map (uncurry prettyNotEq) csNotEq
        ++ map (uncurry prettyMetaEq) (M.toList csMetaEq)
        ++ map prettyNative csNative
    where
      prettyAssignment v t = pretty v <+> ":=" <+> pretty t
      prettyMetaEq v u = pretty v <+> "~~" <+> pretty u
      prettyNotEq v u = pretty v <+> "/=" <+> pretty u
      prettyNative n = pretty (show n)

-- | Calling @conjunct c cs@ will return @Nothing@ if the addition of @c@ into the
--  constraint set @cs@ makes it provably UNSAT. If @conjunct c cs == Just cs'@, there
--  is /no guarantee/ that @cs'@ is SAT, you must still validate it on a SMT solver.
conjunct ::
  forall lang meta.
  (Language lang, Pretty meta, Ord meta) =>
  Constraint lang meta ->
  ConstraintSet lang meta ->
  Maybe (ConstraintSet lang meta)
conjunct c cs0 =
  case c of
    Assign v t -> unifyMetaWith cs0 v t
    TermEq t u -> unifyWith cs0 t u
    -- TODO: Actually... we could be calling the smt solver right here to check that this
    -- sexpr is consistent with cs0, but let's leave that for later.
    Native sexpr -> Just $ cs0 {csNative = sexpr : csNative cs0}
    TermNotEq t u -> Just $ cs0 {csNotEq = (t, u) : csNotEq cs0}
  where
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
      iterateM cs $ zipWith (\x y cs' -> unifyArgWith cs' x y) argsT argsU
      where
        iterateM :: (Monad m) => a -> [a -> m a] -> m a
        iterateM a [] = return a
        iterateM a (f : fs) = f a >>= flip iterateM fs
    unifyWith _ t u =
      error $
        "unifyWith:\n"
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
    unifyMetaWith cs v u
      -- First we check whether @v@ is actually equal to anything else
      | Just t <- M.lookup v (csAssignments cs) = unifyWith cs t u
      -- If not, we check whether v is equivalent to some other smaller metavariable
      | Just v' <- M.lookup v (csMetaEq cs) = unifyMetaWith cs v' u
      | otherwise = Just $ unifyNewMetaWith cs v u

    -- Like 'unifyMetaWith', but assumes that the 'meta' in question is not
    -- known by our current constraints.
    unifyNewMetaWith ::
      ConstraintSet lang meta ->
      meta ->
      TermMeta lang meta ->
      ConstraintSet lang meta
    unifyNewMetaWith cs@ConstraintSet {..} v (SystF.App (SystF.Meta u) [])
      | v == u = cs
      | Just t <- M.lookup u csAssignments = cs {csAssignments = M.insert v t csAssignments}
      | Just u' <- M.lookup u csMetaEq = unifyNewMetaWith cs v (SystF.App (SystF.Meta u') [])
      | otherwise = cs {csMetaEq = M.insert (max v u) (min v u) csMetaEq}
    unifyNewMetaWith cs v u =
      cs {csAssignments = M.insert v u (csAssignments cs)}

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
  M.lookup v (csAssignments cs)
    <|> (M.lookup v (csMetaEq cs) >>= expandDefOf cs)

-- | Since the translation of individual constraints can fail,
-- the translation of constraints does not always carry all the information it could.
-- So the boolean indicates if every atomic constraint have been translated.
-- A 'False' indicates that some have been forgotten during the translation.
constraintSetToSExpr ::
  forall lang meta m.
  (LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  S.Set Name ->
  ConstraintSet lang meta ->
  m (Bool, UsedAnyUFs, PureSMT.SExpr)
constraintSetToSExpr knownNames ConstraintSet {..} = do
  eAssignments <- mapM (runTranslator . uncurry trAssignment) $ M.toList csAssignments
  eNotEq <- mapM (runTranslator . uncurry trNotEq) csNotEq
  let es = eAssignments ++ eNotEq
  let (trs, usedUFs) = unzip (rights es)
  let eEquivalences = map (uncurry trSymVarEq) $ M.toList csMetaEq
  return (all isRight es, mconcat usedUFs, PureSMT.andMany (csNative ++ eEquivalences ++ trs))
  where
    trNotEq :: TermMeta lang meta -> TermMeta lang meta -> TranslatorT m PureSMT.SExpr
    trNotEq tx ty = do
      tx' <- translateTerm knownNames tx
      ty' <- translateTerm knownNames ty
      return $ PureSMT.not (tx' `PureSMT.eq` ty')

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

data Constraint lang meta
  = Assign meta (TermMeta lang meta)
  | TermEq (TermMeta lang meta) (TermMeta lang meta)
  | TermNotEq (TermMeta lang meta) (TermMeta lang meta)
  | Native PureSMT.SExpr

symVarEq :: meta -> meta -> Constraint lang meta
symVarEq x y = Assign x (SystF.App (SystF.Meta y) [])

termEq :: TermMeta lang meta -> TermMeta lang meta -> Constraint lang meta
termEq = TermEq

termNotEq :: TermMeta lang meta -> TermMeta lang meta -> Constraint lang meta
termNotEq = TermNotEq

native :: PureSMT.SExpr -> Constraint lang meta
native = Native

(=:=) :: meta -> TermMeta lang meta -> Constraint lang meta
a =:= t = Assign a t

instance (LanguagePretty lang, Pretty meta) => Pretty (Constraint lang meta) where
  pretty _ = "<constraint>"

{-

-- TODO: this module should probably be refactored somewhere;
-- I'm not entirely onboard with the 'translateData' funct as it is;
--   a) maybe we should pass the env when translating arbitrary expressions
--   b) maybe we should even keep the env in another reader layer on SolverT...
--
-- Its somthing to think about later, but for now this will do.

-- | Constraints of a path during symbolic execution
-- We would like to have
-- type Constraint = Bot | And (Map Name [PirTerm]) [(Fuel, PirTerm, PirTerm))]
-- It is isomorphic to our current type, but with better access time to the variable assignements.
-- The 2 kinds of equalities are quite different,
-- one represents the complete execution of a branch, which leads to an application which cannot be further inlined
-- (Because it is a builtin or a constant),
-- whereas the other one represents an ongoing computation killed by lack of fuel.
data AtomicConstraint lang meta
  = Assign meta (TermMeta lang meta)
  | VarEq meta meta
  | NonInlinableSymbolEq (TermMeta lang meta) (TermMeta lang meta)
  | NonInlinableSymbolNotEq (TermMeta lang meta) (TermMeta lang meta)
  | OutOfFuelEq (TermMeta lang meta) (TermMeta lang meta)
  | Native PureSMT.SExpr
  deriving (Eq, Show)

data Constraint lang meta
  = And [AtomicConstraint lang meta]
  | Bot
  deriving (Eq, Show)

-- Essentially list concatenation, with the specificity that `Bot` is absorbing.
andConstr :: Constraint lang meta -> Constraint lang meta -> Constraint lang meta
andConstr Bot _ = Bot
andConstr _ Bot = Bot
andConstr (And l) (And m) = And (l ++ m)

instance (LanguagePretty lang, Pretty meta) => Pretty (AtomicConstraint lang meta) where
  pretty (Assign n term) =
    pretty n <+> "↦" <+> pretty term
  pretty (VarEq a b) =
    pretty a <+> "⇔" <+> pretty b
  pretty (NonInlinableSymbolEq t u) =
    pretty t <+> "==" <+> pretty u
  pretty (NonInlinableSymbolNotEq t u) =
    pretty t <+> "/=" <+> pretty u
  pretty (OutOfFuelEq t u) =
    pretty t <+> "~~" <+> pretty u
  pretty (Native expr) =
    pretty $ show expr

instance (LanguagePretty lang, Pretty meta) => Pretty (Constraint lang meta) where
  pretty Bot =
    "⊥"
  pretty (And []) =
    "⊤"
  pretty (And l) =
    mconcat $ intersperse "\n∧ " (map pretty l)

-- | Declare constants and assertions in an SMT solver based on a constraint
-- that characterizes a path in the symbolic execution of a Plutus IR term.
--
-- We cannot just generate SExpr for smtlib (instantiating the Translatable
-- class) because of Assign constraints which need to declare names as a side
-- effect and And constraints which need to run these declarations in the right
-- order.
--
-- There is an issue for now when generating assertions such as:
-- x : [Bool]
-- x = Nil
-- because Nil has type List a. Nil must be applied to Bool.
--
-- There are three ways to sort things out:
--
-- 1. Use SMTlib's "match" term
-- e.g. assert ((match x ((Nil true) ((Cons y ys) false))))
--
-- 2. Use the weird "as" SMTLib term
-- assert (= x (as Nil (List Bool)))
-- The weird thing is that Cons should be "cast"/"applied"/"coerced" (which is
-- right?) to List Bool as well although it is a constructor of arity > 0
-- The "as" term seems to mean "here *** is a constructor of that concrete
-- type", but it is not type application
--
-- 3. Use the, weird as well, "_ is" template/function/whatever
-- (assert ((_ is Nil) x))
-- In our case, it seems to be a shortcut that is equivalent to #1
--
-- All these solutions could lead to the same sat result and examples.
-- However, solution #2 presents the advantage that it allows to give names to the argument of constructors,
-- which can then be used in further constraints.
--
-- Hence, we chose solution #2
atomicConstraintToSExpr ::
  (LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  S.Set Name ->
  AtomicConstraint lang meta ->
  TranslatorT m PureSMT.SExpr
atomicConstraintToSExpr knownNames (Assign name term) = do
  let smtName = translate name
  d <- translateTerm knownNames term
  return $ smtName `PureSMT.eq` d
atomicConstraintToSExpr _knownNames (VarEq a b) = do
  let aName = translate a
  let bName = translate b
  return $ aName `PureSMT.eq` bName
atomicConstraintToSExpr knownNames (NonInlinableSymbolEq term1 term2) = do
  t1 <- translateTerm knownNames term1
  t2 <- translateTerm knownNames term2
  return $ t1 `PureSMT.eq` t2
atomicConstraintToSExpr knownNames (NonInlinableSymbolNotEq term1 term2) = do
  t1 <- translateTerm knownNames term1
  t2 <- translateTerm knownNames term2
  return $ PureSMT.not (t1 `PureSMT.eq` t2)
atomicConstraintToSExpr knownNames (OutOfFuelEq term1 term2) = do
  t1 <- translateTerm knownNames term1
  t2 <- translateTerm knownNames term2
  return $ t1 `PureSMT.eq` t2
atomicConstraintToSExpr _knownNames (Native expr) =
  return expr

constraintToSExpr ::
  (LanguageSMT lang, ToSMT meta, PirouetteReadDefs lang m) =>
  S.Set Name ->
  Constraint lang meta ->
  m (Bool, UsedAnyUFs, PureSMT.SExpr)
constraintToSExpr knownNames (And constraints) = do
  atomTrads <- mapM (runTranslator . atomicConstraintToSExpr knownNames) constraints
  let (translations, usedUFs) = unzip (rights atomTrads)
  return (all isRight atomTrads, mconcat usedUFs, PureSMT.andMany translations)
constraintToSExpr _ Bot = return (True, NotUsedAnyUFs, PureSMT.bool False)

-}
