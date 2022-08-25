{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Transformations.Monomorphization where

import Control.Arrow (second)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Generics.Uniplate.Data
import Data.List (isPrefixOf)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Utils

-- * Monomorphization

-- | Given a set of definitions in prenex form (i.e., all 'SystF.TyAll' appear in the front and
-- you can rely on "Pirouette.Transformations.Prenex" to get there), will yield a new set
-- of definitions that contains no 'SystF.TyAll' nor datatypes of kind other than *.
monomorphize :: forall lang. (Language lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
monomorphize defs0 = prune $ go mempty defs0
  where
    defsToMono = selectMonoDefs defs0

    -- This fixpoint is necessary since we might encounter things such as:
    --
    -- > length :: [a] -> Int
    -- > f :: [a] -> Int
    -- > f x = ... (length x) ...
    -- > main = f [3] + f "abc"
    --
    -- On a first iteration, we'll learn that we should specialize 'f' twice:
    -- once for @a ~ Integer@ and once for @a ~ Char@. Now, however we'll have
    -- calls to @length@ which are applied to different type-variables, hence,
    -- we need to run again.
    go :: S.Set (SpecRequest lang) -> PrtUnorderedDefs lang -> PrtUnorderedDefs lang
    go prevOrders defs
      | M.null newDefs && defs == defs' = defs'
      | otherwise = go (prevOrders <> S.fromList newOrders) $ addDecls newDefs defs'
      where
        (defs', specOrders) =
          runWriter $
            transformBiM (specFunApp defsToMono) defs
              >>= transformBiM (specTyApp defsToMono)
        newOrders = filter (`S.notMember` prevOrders) specOrders
        newDefs = foldMap executeSpecRequest newOrders

    prune :: PrtUnorderedDefs lang -> PrtUnorderedDefs lang
    prune defs = defs {prtUODecls = M.filterWithKey (\n _ -> n `M.notMember` defsToMono) $ prtUODecls defs}

-- | Picks all definitions that should be monomorphized.
--  Right now, any polymorphic definition (be it a function or a type) is subject to monomorphization.
--  This function also picks up associated definitions that should be monomorphized
--  (constructors and destructors for types),
--  but associates them with no particular definition.
--
--  Moreover, it is important to keep the 'Namespace' in the map, otherwise we might
--  run into scenarios where a type that has a homonym constructor might not be
--  monomorphized becase one entry overriden the other in the map.
selectMonoDefs ::
  forall lang.
  (Language lang) =>
  PrtUnorderedDefs lang ->
  M.Map (Namespace, Name) (Maybe (FunOrTypeDef lang))
selectMonoDefs PrtUnorderedDefs {..} =
  let defsList = mapMaybe (secondM isFunOrTypeDef) $ M.toList prtUODecls
      -- Makes a first selection of definitions: all of those satisfying 'shouldMono'
      selectedDefs0 = filter (shouldMono . snd) defsList
      -- Now get all constructor/destructor names that are associated with
      -- the typedefs from selectedNames0, but we associate them with
      associatedNames =
        [ ((TermNamespace, name), Nothing)
          | (_, SystF.TyArg tydef) <- selectedDefs0,
            name <- destructor tydef : map fst (constructors tydef)
        ]
   in M.fromList $ associatedNames <> map (second Just) selectedDefs0

type FunOrTypeDef lang = SystF.Arg (TypeDef lang) (FunDef lang)

-- | Returns whether we should monomorphize this function or type.
--
-- Any polymorphic function and any type with type variables is subject to monomorphization.
shouldMono :: FunOrTypeDef lang -> Bool
shouldMono (SystF.TermArg FunDef {..}) = isPolyType funTy
shouldMono (SystF.TyArg Datatype {..}) = not (null typeVariables)

isPolyType :: SystF.AnnType ann ty -> Bool
isPolyType SystF.TyAll {} = True
isPolyType _ = False

isFunOrTypeDef :: Definition lang -> Maybe (FunOrTypeDef lang)
isFunOrTypeDef (DTypeDef tydef) = Just (SystF.TyArg tydef)
isFunOrTypeDef (DFunDef fdef) = Just (SystF.TermArg fdef)
isFunOrTypeDef _ = Nothing

-- * Specializer

-- | Describes a definition (a function or a type) that needs to be specialized
-- with the given type arguments list. The specialized definitions are generated
-- through 'executeSpecRequest'
data SpecRequest lang = SpecRequest
  { srName :: Name,
    srOrigDef :: FunOrTypeDef lang,
    srArgs :: [Type lang]
  }
  deriving (Show, Eq, Ord)

-- | Specializes a function application of the form:
--
--  > f @Integer @Bool x y z
--
-- at call site.
--
-- The function assumes the program is in the prenex form (as all other parts of this transformation do).
--
-- This function only does the substitution _at call site_ and emits a 'SpecRequest' denoting that the corresponding
-- _definition_ needs to be specialized (which will be handled later by 'executeSpecRequest').
specFunApp ::
  (MonadWriter [SpecRequest lang] m, Language lang) =>
  M.Map (Namespace, Name) (Maybe (FunOrTypeDef lang)) ->
  Term lang ->
  m (Term lang)
specFunApp toMono (SystF.App (SystF.Free (TermSig name)) args)
  -- We compare the entire name, not just the nameString part: x0 /= x1.
  | Just mSomeDef <- (TermNamespace, name) `M.lookup` toMono,
    -- Now we ensure that there is something to specialize and that the type arguments we've
    -- gathered are specializable arguments (ie, no bound type-variables)
    let tyArgs = map (fromJust . SystF.fromTyArg) $ takeWhile SystF.isTyArg args,
    not (null tyArgs),
    all isSpecArg tyArgs = do
    let (specArgs, remainingArgs) = SystF.splitArgs (length tyArgs) args
        speccedName = genSpecName specArgs name
    tell $ maybe [] (\someDef -> pure $ SpecRequest name someDef specArgs) mSomeDef
    pure $ SystF.Free (TermSig speccedName) `SystF.App` remainingArgs
specFunApp _ x = pure x

-- | Specializes a type application of the form
--
--  > HOFType @Integer
--
--  See the docs for 'specFunApp' for more details.
specTyApp ::
  (MonadWriter [SpecRequest lang] m, Language lang) =>
  M.Map (Namespace, Name) (Maybe (FunOrTypeDef lang)) ->
  Type lang ->
  m (Type lang)
specTyApp toMono (SystF.TyApp (SystF.Free (TySig name)) tyArgs)
  | Just mSomeDef <- (TypeNamespace, name) `M.lookup` toMono,
    not (null tyArgs),
    all isSpecArg tyArgs = do
    let (specArgs, remainingArgs) = splitAt (length tyArgs) tyArgs
        speccedName = genSpecName specArgs name
    tell $ maybe [] (\someDef -> pure $ SpecRequest name someDef specArgs) mSomeDef
    pure $ SystF.Free (TySig speccedName) `SystF.TyApp` remainingArgs
specTyApp _ x = pure x

specRequestPartialApp :: SpecRequest lang -> Term lang
specRequestPartialApp SpecRequest {..} =
  SystF.App (SystF.Free $ TermSig srName) $ map SystF.TyArg srArgs

-- Below is an useful definition for debugging specialization requests, just rename
-- the original one to executeSpecRequest'
-- executeSpecRequest :: (Language lang) => SpecRequest lang -> Decls lang
-- executeSpecRequest sr =
--   let res = executeSpecRequest' sr
--       str =
--         unlines
--           [ "---------------------------------",
--             "executeSpecRequest: ",
--             "  " ++ show (pretty $ specRequestPartialApp sr),
--             "result:",
--             show (pretty res)
--           ]
--    in trace str res

-- | Takes a description of what needs to be specialized
-- (a function or a type definition along with specialization args)
-- and produces the specialized definitions.
executeSpecRequest :: (Language lang) => SpecRequest lang -> Decls lang
executeSpecRequest SpecRequest {..} = M.fromList $
  case srOrigDef of
    SystF.TermArg FunDef {..} ->
      let newDef =
            DFunction
              funIsRec
              (funBody `SystF.appN` map SystF.TyArg srArgs)
              (funTy `SystF.tyInstantiateN` srArgs)
       in [((TermNamespace, fixName srName), newDef)]
    SystF.TyArg Datatype {..} ->
      let tyName = fixName srName
          dtorName = fixName destructor
          ctors =
            [ (fixName ctorName, fixType $ ctorTy `SystF.tyInstantiateN` srArgs)
              | (ctorName, ctorTy) <- constructors
            ]
          newDef =
            DTypeDef $
              Datatype
                (SystF.kindDrop specArgsLen kind)
                (drop specArgsLen typeVariables)
                (fixName destructor)
                ctors -- TODO does this only apply to `kind ~ *`?
       in -- trace (show specArgs) $
          [ ((TypeNamespace, tyName), newDef),
            ((TermNamespace, dtorName), DDestructor tyName)
          ]
            <> [ ((TermNamespace, ctorName), DConstructor i tyName)
                 | (ctorName, _) <- ctors
                 | i <- [0 ..]
               ]
  where
    fixName = genSpecName srArgs
    specArgsLen = length srArgs

    -- When specializing constructor types, we need to substitute occurences of
    -- the un-specialized type with the fixed name. For instance, if we're specializing
    -- a constructor:
    --
    -- > Bin : all a : Type . Bin a -> Bin a -> Bin a
    --
    -- that was applied to TyBool, the result has to be:
    --
    -- > Bin@TyBool : Bin@TyBool -> Bin@TyBool -> Bin@TyBool
    --
    fixType = rewrite $ \case
      SystF.TyApp (SystF.Free (TySig n)) xs -> do
        guard (n == srName && srArgs `isPrefixOf` xs)
        return $ SystF.Free (TySig $ fixName n) `SystF.TyApp` drop specArgsLen xs
      _ -> Nothing

-- | A type argument is fully specialized if it has no bound variables
-- nor type application with any arguments.
isSpecArg :: forall lang. LanguageBuiltins lang => Type lang -> Bool
isSpecArg (SystF.TyApp v []) = isNothing $ isBound v
isSpecArg (SystF.TyFun a b) = isSpecArg a && isSpecArg b
isSpecArg _ = False

-- | This is the set of characters used when generating specialized names
--  when monomorphizing. Because we need to be able to test monomorphization, this
--  is also recognized by the "Language.Pirouette.Example" as a valid part of an identifier
monoNameSep :: [Char]
monoNameSep = ['<', '>', '$', '_', '!'] -- TODO: get rid of '!'

-- | Generates a specialized name for a certain amount of type arguments. This
-- function is trickier than what meets the eye since it must satisfy a homomorphism
-- property. Say we're specializing a type @F a@, applied to @Maybe Bool@.
-- We'll generate a new type, named: @genSpecName [ [ty| Maybe Bool |] ] "F"@,
-- What if, we actually happened to specialize @Maybe Bool@ first? Now,
-- we're specializing @F@ applied to @genSpecName [ [ty| Bool |] ] "Maybe"@.
--
-- We can either choose to control the order in which specialization happens,
-- alwasy specializing "smaller" types first or we make sure that that order
-- doesn't matter by generating the same name regardless. Currently, we choose
-- the later.
genSpecName :: forall lang. (Language lang) => [Type lang] -> Name -> Name
genSpecName tys n0 = combine n0 (map specTypeNames tys)
  where
    -- Note to future maintainer: make sure all characters used here can be
    -- part of a SMTLIB identfiier!

    combine :: Name -> [Name] -> Name
    combine hd [] = hd
    combine hd ns = hd <> "<" <> mconcat (L.intersperse "$" ns) <> ">"

    specTypeNames :: Type lang -> Name
    specTypeNames (SystF.Free n `SystF.TyApp` args) = genSpecName args (tyBaseName n)
    specTypeNames (SystF.TyFun a b) = specTypeNames a <> "_" <> specTypeNames b
    specTypeNames arg = error $ "unexpected specializing " <> show (pretty arg)

argsToStr :: (LanguageBuiltins lang) => [Type lang] -> T.Text
argsToStr = T.intercalate msep . map f
  where
    msep = T.pack "$"

    f (SystF.Free n `SystF.TyApp` args) =
      nameString (tyBaseName n) <> if null args then mempty else "<" <> argsToStr args <> ">"
    f (SystF.TyFun a b) = f a <> "_" <> f b
    f arg = error $ "unexpected specializing arg" <> show arg

tyBaseName :: LanguageBuiltins lang => TypeBase lang -> Name
tyBaseName (TyBuiltin bt) = Name (T.pack $ show bt) Nothing
tyBaseName (TySig na) = na
