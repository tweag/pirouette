{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Symbolic.Eval.Types where

import Control.Applicative hiding (Const)
import Control.Monad (ap, (>=>))
import Data.Data hiding (eqT)
import Data.Default
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.String (IsString)
import Pirouette.Monad
import qualified Pirouette.SMT as SMT
import qualified Pirouette.Symbolic.Eval.Constraints as Cs
import Pirouette.Term.Syntax
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT

-- | The intermediate datastructure of our symbolic engine, produced by
-- the 'Pirouette.Symbolic.Eval.Anamorphism.symbolically' anamorphism and
-- meant to be consumed by the functions in "Pirouette.Symbolic.Eval.Catamorphism".
-- It denotes a set of pairs of values of language @lang@ and the @Constraint lang@
-- that lead to them.
data TermSet lang
  = Union [TermSet lang]
  | Learn (DeltaEnv lang) (TermSet lang)
  | -- TODO: having the term structure is nice and all, but
    -- we never have any Lam in here at all; Maybe a dedicated @WHNFLayer@ datatype
    -- would be a little more interesting.
    Spine (WHNFLayer lang (TermSet lang))
  | Call Name ([TermSet lang] -> TermSet lang) [TermSet lang]
  | -- TODO: Why not merge 'Call' and 'Dest'? 'Call' is just the semantics of destructing
    -- a function type, and 'Lam' is its respective constructor. This would require some careful
    -- thought, though: do we go into binary application? do we keep this n-ary representation?
    Dest ((ConstructorInfo, [TermSet lang]) -> TermSet lang) (TermSet lang)
  | -- The maybe represent rigid versus flexible metavariables. Flexible metas
    -- are those that we can continue expanding ad-infinitum, for instance, imagine
    -- a meta @k@ of type @[Int]@, we can always expand @k = j : k'@, and continue
    -- expanding @k'@, but we can't expand @j@ since it's of a builtin type
    Inst SymVar (Maybe (TermSet lang))

-- The show instance is here only to satisfy some class constraints,
-- for inspection and debugging, make sure to rely on the pretty instance.
instance Show (TermSet lang) where
  show _ = "<termset>"

instance LanguagePretty lang => Pretty (TermSet lang) where
  pretty (Union tss) =
    hang 1 $ vsep $ "Union" : map (("-" <+>) . pretty) tss
  pretty (Learn d ts) =
    hang 1 $ vsep ["Learn " <+> pretty d, pretty ts]
  pretty (Spine l) = pretty l
  pretty (Call f _ _) = "Call" <+> pretty f
  pretty (Dest _ x) =
    hang 1 $ vsep ["Match", pretty x]
  pretty (Inst sv _) = "Inst" <+> pretty sv

data WHNFLayer lang x
  = WHNFCotr ConstructorInfo [x]
  | WHNFBuiltin (BuiltinTerms lang) [x]
  | WHNFConst (Constants lang)
  | WHNFBottom

instance (LanguagePretty lang, Pretty x) => Pretty (WHNFLayer lang x) where
  pretty WHNFBottom = "bottom"
  pretty (WHNFCotr ci args) = parens $ sep $ (pretty ci :) $ map pretty args
  pretty (WHNFBuiltin ci args) = parens $ sep $ (pretty ci :) $ map pretty args
  pretty (WHNFConst c) = pretty c

data WHNFTerm lang
  = WHNFMeta SymVar
  | WHNFLayer (WHNFLayer lang (WHNFTerm lang))

instance (LanguagePretty lang) => Pretty (WHNFTerm lang) where
  pretty (WHNFMeta s) = pretty s
  pretty (WHNFLayer t) = pretty t

data ConstructorInfo = ConstructorInfo
  { ciTyName :: TyName,
    ciCtorName :: Name,
    ciCtorIx :: Int
  }
  deriving (Eq, Ord, Show)

instance Pretty ConstructorInfo where
  pretty = pretty . ciCtorName

-- | A 'DeltaEnv' represents a small addition to the current environment; catamorphisms
-- are free to process these however way they see fit.
data DeltaEnv lang
  = DeclSymVars (M.Map SymVar (Type lang))
  | Assign SymVar (TermMeta lang SymVar)
  deriving (Eq, Show)

instance LanguagePretty lang => Pretty (DeltaEnv lang) where
  pretty (DeclSymVars ds) = hsep $ punctuate ";" (map (\(s, t) -> pretty s <+> ":" <+> pretty t) $ M.toList ds)
  pretty (Assign s t) = pretty s <+> ":=" <+> pretty t

-- | Options to run the symbolic engine with. This includes options for tunning the behavior
-- of the SMT solver and internals of the symbolic execution engine.
data Options = Options
  { -- | Specifies the command, number of workers and whether to run PureSMT in debug mode, where
    --  all interactions with the solvers are printed
    optsPureSMT :: PureSMT.Options,
    -- | Specifies the stopping condition for the symbolic engine. By default, it is: 50
    --  That is, we stop exploring any branch where we assignment more than 50 symbolic variables.
    maxAssignments :: Integer
  }

optsSolverDebug :: Options -> Options
optsSolverDebug opts =
  opts {optsPureSMT = (optsPureSMT opts) {PureSMT.debug = True}}

instance Default Options where
  def = Options def 50

-- | The 'LanguageSymEval' class is used to instruct the symbolic evaluator on how to branch on certain builtins.
-- It is inherently different from 'SMT.LanguageSMT' in the sense that, for instance, the 'SMT.LanguageSMT'
-- translation of a primitive @if@ statement might use the @ifthenelse@ SMT primitive.
-- If you just rely on the SMT @ifthenelse@ construct for symbolic evaluation, though, you might end up receiving
-- bogus counter-examples due to the SMT assuming wrong things out of uninterpreted functions
-- due to a lack of information.
--
-- Say we translate the builtin @if@ statement to its SMT counterpart and evaluate:
--
-- > (assert (= x (ifthenelse (isEven 5) 42 0)))
-- > (assert (= x 0))
-- > (check-sat)
--
-- The SMT will say the above is unsat, and will give a model that assumes @isEven 5@ to be true,
-- yielding @x = 42@. That's because @isEven@ is an uninterpreted function, so the SMT has no information
-- about it.
--
-- The rule of thumb is easy: any primitive of your language that should branch the symbolic execution engine
-- should receive special treatment in 'LanguageSymEval'; branching should always be handled by the symbolic
-- engine and never delegated to the SMT solver. In this example, the 'LanguageSymEval' should instruct
-- the symbolic evaluation engine on how to branch when that primitive is found.
-- In particular, two branches should be created:
--
--   1. Add @condition = True@ to the list of known things, continue with the then term,
--   2. Add @condition = False@ to the list of known things, continue with the else term.
--
-- This is the topmost class in the Pirouette universe, the relation between all the classes is:
--
-- > LanguageBuiltins --> defines the built-ins (both terms and types)
-- >   |     \
-- >   |      LanguageBuiltinTypes --> defines the typing rules of each built-in term
-- >   |
-- > LanguageSMT --> defines translation of built-ins into SMT
-- >   |             (not every term can be translated)
-- >   |
-- > LanguageSymEval --> defines at which points the symbolic evaluator has to do sth. special
--
-- If you require nothing special for your particular language, defining:
--
-- > branchesBuiltinTerm _ _ _ = pure Nothing
--
-- is a fine implementation
class (SMT.LanguageSMT lang) => LanguageSymEval lang where
  -- | Injection of different cases in the symbolic evaluator.
  -- For example, one can introduce a 'if_then_else' built-in
  -- and implement this method to look at both possibilities; or
  -- can be used to instruct the solver to branch on functions such
  -- as @equalsInteger :: Integer -> Integer -> Bool@, where @Bool@
  -- might not be a builtin type.
  branchesBuiltinTerm ::
    (PirouetteReadDefs lang m) =>
    -- | Head of the application to translate
    BuiltinTerms lang ->
    -- | Arguments of the application to translate
    [WHNFTerm lang] ->
    -- | If 'Nothing', this means that this built-in term does not require anything special from the
    -- symbolic evaluator. For example, it might be that it's translated fine by 'LanguageSMT'.
    -- If 'Just', it provides information of what to assume in each branch and the term to
    -- symbolically evaluate further.
    m (Maybe [([DeltaEnv lang], WHNFTerm lang)])

  -- | Casts a boolean in @lang@ to a boolean in SMT by checking whether it is true.
  --  Its argument is the translation of a term of type "Bool" in @lang@.
  --  If your language has booleans as a builtin and you defined their interpretation into SMTLIB as
  --  builtin SMT booleans, this function will be just @id@, otherwise, you might
  --  want to implement it as something such as @\x -> PureSMT.eq x (myTrue `PureSMT.as` myBool)@
  --
  --  This function is meant to be used with @-XTypeApplications@
  isTrue :: PureSMT.SExpr -> PureSMT.SExpr

-- * Older Types

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Ord, Show, Data, Typeable, IsString)

instance Pretty SymVar where
  pretty = pretty . symVar

instance SMT.ToSMT SymVar where
  translate = SMT.translate . symVar

type Constraint lang = Cs.Constraints lang SymVar

data PathStatus = Completed | OutOfFuel deriving (Eq, Show)

instance Pretty PathStatus where
  pretty Completed = "Completed"
  pretty OutOfFuel = "OutOfFuel"

data Path lang res = Path
  { pathConstraint :: Constraint lang,
    pathGamma :: M.Map Name (Type lang),
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

deriving instance (Eq (Constraint lang), Eq (Type lang), Eq res) => Eq (Path lang res)

deriving instance (Show (Constraint lang), Show (Type lang), Show res) => Show (Path lang res)

instance (LanguagePretty lang, Pretty a) => Pretty (Path lang a) where
  pretty (Path conds gamma res) =
    vsep
      [ "Env:" <+> hsep (map pretty (M.toList gamma)),
        "Conds:" <+> indent 2 (pretty conds),
        "Tip:" <+> indent 2 (pretty res)
      ]

data AvailableFuel = Fuel Int | InfiniteFuel
  deriving (Eq, Show)

data SymEvalSt lang = SymEvalSt
  { sestConstraint :: Constraint lang,
    sestGamma :: M.Map Name (Type lang),
    sestAssignments :: Integer,
    -- | The set of names the SMT solver is aware of
    sestKnownNames :: S.Set Name
  }

instance Semigroup (SymEvalSt lang) where
  SymEvalSt c1 g1 a1 n1 <> SymEvalSt c2 g2 a2 n2 =
    SymEvalSt
      (c1 <> c2)
      -- (M.unionWithKey (\k _ _ -> error $ "Key already declared: " ++ show k) g1 g2)
      (M.union g1 g2)
      (max a1 a2)
      (n1 <> n2)

instance Monoid (SymEvalSt lang) where
  mempty = SymEvalSt mempty M.empty 0 S.empty

instance Default (SymEvalSt lang) where
  def = SymEvalSt def M.empty 0 S.empty

instance (LanguagePretty lang) => Pretty (SymEvalSt lang) where
  pretty SymEvalSt {..} =
    "Constraints are" <+> pretty sestConstraint <> "\n"
      <> "in environnement"
      <+> pretty (M.toList sestGamma)
      <> "\n"

-- | Given a result and a resulting state, returns a 'Path' representing it.
path :: SymEvalSt lang -> a -> Path lang a
path st x =
  Path
    { pathConstraint = sestConstraint st,
      pathGamma = sestGamma st,
      pathResult = x
    }
