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
import Pirouette.Term.Syntax
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT

-- | The intermediate datastructure of our symbolic engine, produced by
-- the 'Pirouette.Symbolic.Eval.Anamorphism.symbolically' anamorphism and
-- meant to be consumed by the functions in "Pirouette.Symbolic.Eval.Catamorphism".
--
-- It denotes a set of pairs of @TermMeta lang SymVar@ and @Constraint lang@.
newtype TermSet lang = TermSet {unTermSet :: Tree (DeltaEnv lang) (Spine lang (TermSet lang))}

instance Show (TermSet lang) where
  show _ = "<termset>"

-- | A 'SpineTree' is a functor which represents a /set of/ 'Spine's with holes of
-- type @a@. The trick is that once we take the fixpoint of this functor, as in 'TermSet',
-- we now have an infinite structure that alternates between branching and some concrete spines.

-- instance Functor (SpineTree lang) where
--   fmap f = SpineTree . fmap (fmap f) . unSpineTree
--
-- instance Applicative (SpineTree lang) where
--   pure = SpineTree . pure . pure
--   SpineTree fs <*> SpineTree xs = SpineTree $ do
--     spineF <- fs
--     x <- xs
--     return $ spineF <*> x

-- | A @Spine lang meta x@ represents a value in @lang@ with holes of type @x@.
--  The slight trick to you usual representation of values is that we are also representing
--  function and destructor calls explicitely in the tree, leaving the consumer to
--  decide how these values should be computed, depending on the semantics of @lang@.
data Spine lang x
  = -- | A function call, in an untyped setting, can be seen as something
    -- that takes a list of terms and returns a term (in fact, that's the type of
    -- the partially applied 'SystF.App' constructor!).
    --
    -- > [Term lang] -> Term lang
    --
    -- The trick here consists in lifting those functions to trees:
    --
    -- > [Spine lang a] -> Spine lang a
    --
    -- Finally, because we want a monadic structure, we'll go polymorphic:
    Call Name ([Spine lang (TermSet lang)] -> Spine lang x) [Spine lang (TermSet lang)]
  | -- | Destructors are also a little tricky, because in reality, we need to
    -- consume the motive until /at least/ the first constructor is found, that
    -- is the only guaranteed way to make any progress.
    Dest ((ConstructorInfo, [Spine lang (TermSet lang)]) -> Spine lang x) (Spine lang (TermSet lang))
  | Head (WHNFTermHead lang) [Spine lang x]
  | Next x

instance Show (Spine lang x) where
  show _ = "<spine>"

data WHNFTermHead lang
  = WHNFCotr ConstructorInfo
  | WHNFBuiltin (BuiltinTerms lang)
  | WHNFBottom
  | WHNFConst (Constants lang)
  | -- Rigid symvars are those symbolic variables of types weknow no inductive
    -- definition of. For example, builtin integers.
    WHNFSymVar SymVar

instance Functor (Spine lang) where
  fmap f (Call n body args) = Call n (fmap f . body) args
  fmap f (Dest cs motive) = Dest (fmap f . cs) motive
  fmap f (Head hd args) = Head hd (map (fmap f) args)
  fmap f (Next x) = Next (f x)

instance Applicative (Spine lang) where
  pure = Next
  (<*>) = ap

instance Monad (Spine lang) where
  (Next x) >>= h = h x
  (Call n f xs) >>= h = Call n (f >=> h) xs
  (Dest cs mot) >>= h = Dest (cs >=> h) mot
  (Head hd xs) >>= h = Head hd (map (h =<<) xs)

-- instance Functor (TermTree lang meta) where
--   fmap f (TermTree x) = TermTree $ fmap (fmap f) x
--
-- instance Show (SymbTerm lang x) where
--   show _ = "<symbterm>"

-- THE ISSUE:
--
-- When liftedTermAppN takes the following term:
--
-- > λ (n : Nat) (m : Nat) . Nat_match 1#n @Nat 0#m (λ sn : Nat . Suc (add 0#sn 1#m))
--
-- Applied to the following trees:
--
-- > n == Union
-- >    [ Learn (s0 === Zero) (Call (Cotr Zero) []) -- (A)
-- >    , Learn (Fresh s1) (Learn (s0 == Suc s1) (Call (Cotr Suc) ${ ana s1 }))
-- >    ]
-- >
-- > m == Call (Cotr Suc) ${ ana s0 }
--
-- We wold expect to push "Nat_match" down the different combinations, yielding something like:
--
-- > Union
-- >   [ Learn (s0 === Zero) (Leaf $ Nat_match (Call (Ctor Zero) []) @Nat ... )
-- >   , ...
-- >   ]
--
-- And that's the issue! In the first branch of the union, (A) above, there is no 'Leaf' constructor
-- whatsoever, so any sort of distributive law will pull that @Call (Cotr Zero) []@ to the top level with it.
-- Indeed, that's what is happening:
--
-- > result = Union
-- >   [Learn (s0 === Zero) (Call (Cotr Zero) [])
-- >   ,Learn (Fresh s1) (Learn (s0 === Suc s1) (Call (Cotr Suc) #{ ana s1 } )))]
--
-- IDEA: split it up into two functors, which will be mutually recursive (or explicitely fixpointed)
-- This could show us all the /layers/ of the ana, giving us a chance to act productively PER LAYER!

-- deriving instance (LanguageBuiltins lang) => Show (CallHead lang)

-- TODO: Document how we CANNOT put constructors that mirror the term structure because
-- the distributive law would push the term "under evaluation" below constructors. For instance:
-- > Nat_match ${ HypotheticalConstructor X args } ...
-- Would become: @HypotheticalConstructor X { map Nat_match args ... }
-- Which is REALLY different! One is supposed to match on an argument, the other returns a value.

-- TODO: We also depend on terms explicitely on 'Call' and 'Dest' in order to let the
-- cata match on these constructors and have a little more information and freedom to
-- traverse the trees as it wishes. If we were to say something like:
-- > Call :: forall a . ([Tree a] -> Tree b) -> [Tree a] -> Tree b
-- Now, say the cata is looking at a call:
-- > cata (Call f args) = ...
-- We cannot know that args are actually sets of terms and the only things we can do are:
-- 1. evaluate args completely: @Tree [a]@, then apply. Which corresponds to full blown call-by-value and
-- would never terminate in our case.
-- 2. just apply, corresponding to call-by-name.
-- Yet, we might want to do more interesting things such as evaluate up to depth 3 then apply or whatever.

data ConstructorInfo = ConstructorInfo
  { ciTyName :: TyName,
    ciCtorName :: Name,
    ciCtorIx :: Int
  }
  deriving (Eq, Ord, Show)

-- | A 'DeltaEnv' represents a small addition to the current environment; catamorphisms
-- are free to process these however way they see fit.
data DeltaEnv lang
  = DeclSymVars (M.Map SymVar (Type lang))
  | Assign SymVar (TermMeta lang SymVar)
  deriving (Eq, Show)

-- | A 'Tree' which denotes a set of pairs of @(deltas, a)@
data Tree deltas a
  = Leaf a
  | Learn deltas (Tree deltas a)
  | Union [Tree deltas a]
  deriving (Show)

instance Functor (Tree deltas) where
  fmap f (Leaf x) = Leaf $ f x
  fmap f (Union ts) = Union $ map (fmap f) ts
  fmap f (Learn str t) = Learn str $ fmap f t

-- fmap f (Call hd ts as) = Call hd (fmap f . ts) as
-- fmap f (Dest worlds motive) = Dest (fmap f . worlds) motive

instance Applicative (Tree deltas) where
  pure = Leaf
  (<*>) = ap

instance Alternative (Tree deltas) where
  empty = Union []

  Union t <|> Union u = Union (t ++ u)
  Union t <|> u = Union (u : t)
  t <|> Union u = Union (t : u)
  t <|> u = Union [t, u]

instance Monad (Tree deltas) where
  Leaf x >>= f = f x
  Union ts >>= f = Union $ map (>>= f) ts
  Learn str t >>= f = Learn str (t >>= f)

-- Call hd body args >>= f = Call hd (f <=< body) args
-- Dest worlds motive >>= f = Dest (f <=< worlds) motive

-- * Older Types

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

data Flexibility = Flexible | Rigid
  deriving (Show)

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Ord, Show, Data, Typeable, IsString)

instance Pretty SymVar where
  pretty = pretty . symVar

instance SMT.ToSMT SymVar where
  translate = SMT.translate . symVar

type Constraint lang = SMT.Constraint lang SymVar

symVarEq :: SymVar -> SymVar -> Constraint lang
symVarEq a b = SMT.And [SMT.VarEq a b]

(=:=) :: SymVar -> TermMeta lang SymVar -> Constraint lang
a =:= t = SMT.And [SMT.Assign a t]

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
      (M.unionWithKey (\k _ _ -> error $ "Key already declared: " ++ show k) g1 g2)
      (max a1 a2)
      (n1 <> n2)

instance Monoid (SymEvalSt lang) where
  mempty = SymEvalSt mempty M.empty 0 S.empty

instance Default (SymEvalSt lang) where
  def = mempty

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
