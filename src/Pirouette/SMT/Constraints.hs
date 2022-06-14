{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Constraints that we can translate to SMT
module Pirouette.SMT.Constraints where

import Data.Either
import Data.List (intersperse)
import Data.Map (Map)
import Pirouette.Monad
import Pirouette.SMT.Base
import qualified PureSMT
import Pirouette.SMT.Translation
import Pirouette.Term.Syntax
import Prettyprinter hiding (Pretty (..))
import qualified Data.Set as S

-- TODO: this module should probably be refactored somewhere;
-- I'm not entirely onboard with the 'translateData' funct as it is;
--   a) maybe we should pass the env when translating arbitrary expressions
--   b) maybe we should even keep the env in another reader layer on SolverT...
--
-- Its somthing to think about later, but for now this will do.

-- | Bindings from names to types (for the assign constraints)
type Env lang = Map Name (Type lang)

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

instance Semigroup (Constraint lang meta) where
  (<>) = andConstr

instance Monoid (Constraint lang meta) where
  mempty = And []

data Branch lang meta = Branch
  { additionalInfo :: Constraint lang meta,
    newTerm :: TermMeta lang meta
  }

class (LanguageSMT lang) => LanguageSMTBranches lang where
  -- | Injection of different cases in the symbolic evaluator.
  -- For example, one can introduce a 'if_then_else' built-in
  -- and implement this method to look at both possibilities.
  branchesBuiltinTerm ::
    (ToSMT meta, PirouetteReadDefs lang m) =>
    BuiltinTerms lang ->
    (TermMeta lang meta -> m (Maybe PureSMT.SExpr)) ->
    [ArgMeta lang meta] ->
    m (Maybe [Branch lang meta])
  branchesBuiltinTerm _ _ _ = pure Nothing

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

-- Since the translation of atomic constraints can fail,
-- the translation of constraints does not always carry all the information it could.
-- So the boolean indicates if every atomic constraint have been translated.
-- A 'False' indicates that some have been forgotten during the translation.
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
