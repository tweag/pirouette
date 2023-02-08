{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Symbolic.Eval.Types where

import Data.Data hiding (eqT)
import Data.Default
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.String (IsString)
import Pirouette.Monad
import qualified Pirouette.SMT as SMT
import Pirouette.Term.Syntax
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT

-- | Options to run the symbolic engine with. This includes options for tunning the behavior
-- of the SMT solver and internals of the symbolic execution engine.
data Options = Options
  { -- | Specifies the command, number of workers and whether to run PureSMT in debug mode, where
    --  all interactions with the solvers are printed
    optsPureSMT :: PureSMT.Options,
    -- | Specifies the stopping condition for the symbolic engine. By default, it is:
    --
    --  > \stat -> sestConstructors stat > 50
    --
    --  That is, we stop exploring any branch where we unfolded more than 50 constructors.
    shouldStop :: StoppingCondition
  }

optsSolverDebug :: Options -> Options
optsSolverDebug opts =
  opts {optsPureSMT = (optsPureSMT opts) {PureSMT.debug = True}}

instance Default Options where
  def = Options def (\stat -> sestConstructors stat > 50)

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
    (SMT.ToSMT meta, PirouetteReadDefs lang m) =>
    -- | Head of the application to translate
    BuiltinTerms lang ->
    -- | Translation function to SMT, in case you need to recursively translate an argument
    (TermMeta lang meta -> m (Maybe PureSMT.SExpr)) ->
    -- | Arguments of the application to translate
    [ArgMeta lang meta] ->
    -- | If 'Nothing', this means that this built-in term does not require anything special from the
    -- symbolic evaluator. For example, it might be that it's translated fine by 'LanguageSMT'.
    -- If 'Just', it provides information of what to assume in each branch and the term to
    -- symbolically evaluate further.
    m (Maybe [SMT.Branch lang meta])

  -- | Casts a boolean in @lang@ to a boolean in SMT by checking whether it is true.
  --  Its argument is the translation of a term of type "Bool" in @lang@.
  --  If your language has booleans as a builtin and you defined their interpretation into SMTLIB as
  --  builtin SMT booleans, this function will be just @id@, otherwise, you might
  --  want to implement it as something such as @\x -> PureSMT.eq x (myTrue `PureSMT.as` myBool)@
  --
  --  This function is meant to be used with @-XTypeApplications@
  isTrue :: PureSMT.SExpr -> PureSMT.SExpr

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Ord, Show, Data, Typeable, IsString)

instance Pretty SymVar where
  pretty (SymVar n) = pretty n

instance SMT.ToSMT SymVar where
  translate = SMT.translate . symVar

data PathStatus = Completed | OutOfFuel deriving (Eq, Show)

instance Pretty PathStatus where
  pretty Completed = "Completed"
  pretty OutOfFuel = "OutOfFuel"

data Path lang res = Path
  { pathConstraint :: SMT.ConstraintSet lang SymVar,
    pathGamma :: M.Map Name (Type lang),
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

deriving instance (Eq (SMT.ConstraintSet lang SymVar), Eq (Type lang), Eq res) => Eq (Path lang res)

deriving instance (Show (SMT.ConstraintSet lang SymVar), Show (Type lang), Show res) => Show (Path lang res)

instance (LanguagePretty lang, Pretty a) => Pretty (Path lang a) where
  pretty (Path conds _gamma ps res) =
    vsep
      [ "", -- "Env:" <+> hsep (map pretty (M.toList gamma)),
        "Path:" <+> indent 2 (pretty conds),
        "Status:" <+> pretty ps,
        "Tip:" <+> indent 2 (pretty res)
      ]

data AvailableFuel = Fuel Int | InfiniteFuel
  deriving (Eq, Show)

data SymEvalSt lang = SymEvalSt
  { sestConstraint :: SMT.ConstraintSet lang SymVar,
    sestGamma :: M.Map Name (Type lang),
    sestFreshCounter :: Int,
    sestStatistics :: SymEvalStatistics,
    -- | The set of names the SMT solver is aware of
    sestKnownNames :: S.Set Name,
    sestModel :: Maybe Model
  }

instance Default (SymEvalSt lang) where
  def = SymEvalSt def M.empty 0 mempty S.empty Nothing

instance (LanguagePretty lang) => Pretty (SymEvalSt lang) where
  pretty SymEvalSt {..} =
    "Constraints are" <+> pretty sestConstraint <> "\n"
      <> "in environnement"
      <+> pretty (M.toList sestGamma)
      <> "\n"
      <> "with a counter at"
      <+> pretty sestFreshCounter
      <+> "and"
      <+> pretty (sestConsumedFuel sestStatistics)
      <+> "fuel consumed"

data SymEvalStatistics = SymEvalStatistics
  { sestConsumedFuel :: Int,
    sestConstructors :: Int
  }
  deriving (Eq, Show)

type StoppingCondition = SymEvalStatistics -> Bool

instance Semigroup SymEvalStatistics where
  SymEvalStatistics f1 c1 <> SymEvalStatistics f2 c2 =
    SymEvalStatistics (f1 + f2) (c1 + c2)

instance Monoid SymEvalStatistics where
  mempty = SymEvalStatistics 0 0

-- | Given a result and a resulting state, returns a 'Path' representing it.
path :: StoppingCondition -> a -> SymEvalSt lang -> Path lang a
path stop x st =
  Path
    { pathConstraint = sestConstraint st,
      pathGamma = sestGamma st,
      pathStatus = if stop (sestStatistics st) then OutOfFuel else Completed,
      pathResult = x
    }

-- | Models returned by the SMT solver
newtype Model = Model [(PureSMT.SExpr, PureSMT.Value)]
  deriving (Eq, Show)
