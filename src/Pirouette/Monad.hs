{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Monad where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as Lazy
import qualified Control.Monad.State.Strict as Strict
import Data.Data (Data)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import ListT (ListT)
import ListT.Weighted (WeightedListT)
import Pirouette.Monad.Maybe
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF

-- * The Pirouette Monad(s)

--

-- $pirouettemonad
--
-- Here you will find a number of classes that give access to different
-- aspects of the compiler.
--
--   - 'PirouetteBase' provides a good base monad that you can use without thinking twice.
--     It provides a 'MonadError' and a 'MonadLogger' to help debugging.
--
--   - 'PirouetteReadDefs' provides an additional layer where definitions are available
--     read-only. It is read-only because if your code is deliberately changing definitions,
--     it should probably be a separate compilation step that receives the old set of definitions
--     and produces a new set of definitions.
--
-- The pirouette monad provides us with all the relevant type-checking functionality
-- for our translation into TLA.

-- | The error codes that pirouete can raise
data PrtError
  = PENotAType Name
  | PENotATerm Name
  | PEUndefined Name
  | PEMutRecDeps [Name]
  | PEOther String
  deriving (Eq, Show)

prtError :: PrtError -> a
prtError = error . show

-- ** Pirouette Definitions

-- | Whenever we need access to the list of definitions in the current PIR program
--  being compiled, we probably want to use 'PirouetteReadDefs' instead of 'PirouetteBase'
class (LanguageBuiltins lang, Monad m) => PirouetteReadDefs lang m | m -> lang where
  -- | Returns all declarations in scope
  prtAllDefs :: m (Map.Map (Namespace, Name) (Definition lang))

  -- | Returns the main program
  prtMain :: m (Term lang)

-- | Returns the definition associated with a given name. Raises a 'PEUndefined'
--  if the name doesn't exist.
prtDefOf :: (PirouetteReadDefs lang m) => Namespace -> Name -> m (Definition lang)
prtDefOf space n = do
  defs <- prtAllDefs
  case Map.lookup (space, n) defs of
    Nothing -> prtError $ PEUndefined n
    Just x -> return x

prtDefOfAnyNamespace :: (PirouetteReadDefs lang m) => Name -> m (Definition lang)
prtDefOfAnyNamespace n = do
  defs <- prtAllDefs
  let tm = Map.lookup (TermNamespace, n) defs
      ty = Map.lookup (TypeNamespace, n) defs
  case (tm, ty) of
    (Just _, Just _) -> prtError $ PEUndefined n
    (Just t, Nothing) -> pure t
    (Nothing, Just t) -> pure t
    _ -> prtError $ PEUndefined n

prtTypeDefOf :: (PirouetteReadDefs lang m) => Name -> m (TypeDef lang)
prtTypeDefOf n = prtDefOf TypeNamespace n >>= maybe (prtError $ PENotAType n) return . fromTypeDef

prtTermDefOf :: (PirouetteReadDefs lang m) => Name -> m (Term lang)
prtTermDefOf n = prtDefOf TermNamespace n >>= maybe (prtError $ PENotATerm n) return . fromTermDef

prtIsDest :: (PirouetteReadDefs lang m) => Name -> MaybeT m TyName
prtIsDest n = MaybeT $ fromDestDef <$> prtDefOf TermNamespace n

prtIsConst :: (PirouetteReadDefs lang m) => Name -> MaybeT m (Int, TyName)
prtIsConst n = MaybeT $ fromConstDef <$> prtDefOf TermNamespace n

instance {-# OVERLAPPABLE #-} (PirouetteReadDefs lang m) => PirouetteReadDefs lang (Lazy.StateT s m) where
  prtAllDefs = lift prtAllDefs
  prtMain = lift prtMain

instance {-# OVERLAPPABLE #-} (PirouetteReadDefs lang m) => PirouetteReadDefs lang (Strict.StateT s m) where
  prtAllDefs = lift prtAllDefs
  prtMain = lift prtMain

instance {-# OVERLAPPABLE #-} (PirouetteReadDefs lang m) => PirouetteReadDefs lang (ReaderT s m) where
  prtAllDefs = lift prtAllDefs
  prtMain = lift prtMain

instance {-# OVERLAPPABLE #-} (PirouetteReadDefs lang m) => PirouetteReadDefs lang (ListT m) where
  prtAllDefs = lift prtAllDefs
  prtMain = lift prtMain

instance {-# OVERLAPPABLE #-} (PirouetteReadDefs lang m) => PirouetteReadDefs lang (WeightedListT m) where
  prtAllDefs = lift prtAllDefs
  prtMain = lift prtMain

-- | Returns the type of an identifier
typeOfIdent :: (PirouetteReadDefs lang m) => Name -> m (Type lang)
typeOfIdent n = do
  dn <- prtDefOf TermNamespace n
  case dn of
    (DFunction _ _ ty) -> return ty
    (DConstructor i t) -> snd . (!! i) . constructors <$> prtTypeDefOf t
    (DDestructor t) -> destructorTypeFor n <$> prtTypeDefOf t
    (DTypeDef _) -> prtError $ PEOther $ show n ++ " is a type"

-- | Returns the direct dependencies of a term. This is never cached and
--  is computed freshly everytime its called. Say we call @directDepsOf "f"@,
--  for:
--
--  > f x = g x + h
--  > g x = f (x - 1)
--
--  We'll get @Set.fromList [SystF.Arg "g", SystF.Arg "h"]@. If you'd expect to see
--  @SystF.Arg "f"@ in the result aswell, use "Pirouette.Term.TransitiveDeps.transitiveDepsOf" instead.
directDepsOf :: (PirouetteReadDefs lang m) => Name -> m (Set.Set (SystF.Arg Name Name))
directDepsOf n = do
  ndef <- prtDefOfAnyNamespace n
  return $ case ndef of
    DFunction _ t ty -> typeNames ty <> termNames t
    DTypeDef d ->
      Set.unions
        ( flip map (constructors d) $ \(_, c) ->
            Set.unions $ map typeNames (fst $ SystF.tyFunArgs c)
        )
    DConstructor _ tyN -> Set.singleton $ SystF.TyArg tyN
    DDestructor tyN -> Set.singleton $ SystF.TyArg tyN

-- | Just like 'directDepsOf', but forgets the information of whether certain dependency
--  was on a type or a term.
directDepsOf' :: (PirouetteReadDefs lang m) => Name -> m (Set.Set Name)
directDepsOf' = fmap (Set.map (SystF.argElim id id)) . directDepsOf

-- | Returns whether a constructor is recursive. For the
--  type of lists, for example, @Cons@ would be recursive
--  whereas @Nil@ would not.
consIsRecursive :: (PirouetteReadDefs lang m) => TyName -> Name -> m Bool
consIsRecursive ty con = do
  conArgs <- fst . SystF.tyFunArgs <$> typeOfIdent con
  return $ any (\a -> SystF.TyArg ty `Set.member` typeNames a) conArgs

-- | Returns whether a term definition uses itself directly, that is, for
--
--  > f x = g x + h
--  > g x = f (x - 1)
--
--  calling @termIsRecursive "f"@ would return @False@. See 'transitiveDepsOf' if
--  you want to know whether a term is depends on itself transitively.
termIsRecursive :: (PirouetteReadDefs lang m) => Name -> m Bool
termIsRecursive n = Set.member (SystF.TermArg n) <$> directDepsOf n

data WHNFResult lang meta
  = WHNFConstant (Constants lang)
  | WHNFConstructor Int Name [ArgMeta lang meta]

-- | Returns whether a term is in Weak Head Normal Form,
-- that is, a constant or a constructor followed by any arguments.
termIsWHNF :: (PirouetteReadDefs lang m) => TermMeta lang meta -> m (Maybe (WHNFResult lang meta))
termIsWHNF (SystF.App vm args) = case vm of
  SystF.Bound {} -> pure Nothing
  SystF.Meta {} -> pure Nothing
  SystF.Free (Constant c) -> pure $ Just (WHNFConstant c)
  SystF.Free (TermSig n) -> do
    mDef <- prtDefOf TermNamespace n
    case mDef of
      DConstructor ix ty -> pure $ Just (WHNFConstructor ix ty args)
      _ -> pure Nothing
  SystF.Free _ -> pure Nothing
termIsWHNF _ = pure Nothing

-- | Returns whether the term is a meta-variable.
termIsMeta :: TermMeta lang meta -> Maybe meta
termIsMeta (SystF.App (SystF.Meta m) _args) = Just m
termIsMeta _ = Nothing

-- | Returns whether the term begins with a built-in.
termIsBuiltin :: TermMeta lang meta -> Bool
termIsBuiltin (SystF.App (SystF.Free (Builtin _)) _args) = True
termIsBuiltin _ = False

termIsConstant :: TermMeta lang meta -> Bool
termIsConstant (SystF.App (SystF.Free (Constant _)) _args) = True
termIsConstant _ = False

-- | Returns whether a term is in Weak Head Normal Form,
-- that is, a constant or a constructor followed by any arguments.
termIsWHNFOrMeta :: (PirouetteReadDefs lang m) => TermMeta lang meta -> m Bool
termIsWHNFOrMeta tm = do
  let m = termIsMeta tm
  w <- termIsWHNF tm
  return $ isJust m || isJust w

-- *** Implementations for 'PirouetteReadDefs'

-- | Unordered definitions consist in a map of 'Name' to 'PrtDef' and
--  a /main/ term.
data PrtUnorderedDefs lang = PrtUnorderedDefs
  { prtUODecls :: Decls lang,
    prtUOMainTerm :: Term lang
  }
  deriving (Eq, Data, Show)

addDecls :: Decls builtins -> PrtUnorderedDefs builtins -> PrtUnorderedDefs builtins
addDecls decls defs = defs {prtUODecls = prtUODecls defs <> decls}

instance (LanguageBuiltins lang, Monad m) => PirouetteReadDefs lang (ReaderT (PrtUnorderedDefs lang) m) where
  prtAllDefs = asks prtUODecls
  prtMain = asks prtUOMainTerm

instance
  {-# OVERLAPPING #-}
  (LanguageBuiltins lang, Monad m) =>
  PirouetteReadDefs lang (Strict.StateT (PrtUnorderedDefs lang) m)
  where
  prtAllDefs = Strict.gets prtUODecls
  prtMain = Strict.gets prtUOMainTerm

-- | In contrast to ordered definitions, where we have a dependency order
--  for all term and type declarations in 'prtDecls'. That is, given two
--  terms @f@ and @g@, @f@ depends on @g@ if @elemIndex f prtDepOrder > elemIndex g prtDepOrder@,
--  that is, @f@ appears before @g@ in @prtDepOrder@.
data PrtOrderedDefs lang = PrtOrderedDefs
  { prtDecls :: Decls lang,
    prtDepOrder :: [SystF.Arg Name Name],
    prtMainTerm :: Term lang
  }

prtOrderedDefs :: PrtUnorderedDefs lang -> [SystF.Arg Name Name] -> PrtOrderedDefs lang
prtOrderedDefs uod ord = PrtOrderedDefs (prtUODecls uod) ord (prtUOMainTerm uod)

instance (LanguageBuiltins lang, Monad m) => PirouetteReadDefs lang (ReaderT (PrtOrderedDefs lang) m) where
  prtAllDefs = asks prtDecls
  prtMain = asks prtMainTerm

class (PirouetteReadDefs lang m) => PirouetteDepOrder lang m where
  -- | Returns the dependency ordering of the currently declared terms.
  prtDependencyOrder :: m [SystF.Arg Name Name]

instance (LanguageBuiltins lang, Monad m) => PirouetteDepOrder lang (ReaderT (PrtOrderedDefs lang) m) where
  prtDependencyOrder = asks prtDepOrder

getPrtOrderedDefs :: (PirouetteDepOrder lang m) => m (PrtOrderedDefs lang)
getPrtOrderedDefs = PrtOrderedDefs <$> prtAllDefs <*> prtDependencyOrder <*> prtMain

-- * Some useful syntactical utilities

-- | A destructor application has the following form:
--
--  > [d/Type tyArg0 ... tyArgN X ReturnType case0 ... caseK extra0 ... extraL]
--
--  The 'unDest' function splits it up into:
--
--  > Just (d/Type, [tyArg0 .. tyArgN], X, ReturnType, [case0 .. caseK], [extra0 .. extraL])
--
--  Moreover, we already remove the 'SystF.Arg' wrapper for all the predefined argument positions.
--  Only the extra arguments are kept with their 'SystF.Arg' because they could be types or terms.
data UnDestMeta lang meta = UnDestMeta
  { undestName :: Name,
    undestTypeName :: TyName,
    undestTypeArgs :: [TypeMeta lang meta],
    undestDestructed :: TermMeta lang meta,
    undestReturnType :: TypeMeta lang meta,
    undestCases :: [TermMeta lang meta],
    undestCasesExtra :: [ArgMeta lang meta]
  }

unDest :: (PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (UnDestMeta lang meta)
unDest (SystF.App (SystF.Free (TermSig n)) args) = do
  tyN <- prtIsDest n
  Datatype _ _ _ cons <- lift (prtTypeDefOf tyN)
  let nCons = length cons
  let (tyArgs, args1) = span SystF.isTyArg args
  tyArgs' <- mapM (wrapMaybe . SystF.fromTyArg) tyArgs
  case args1 of
    (SystF.TermArg x : SystF.TyArg retTy : casesrest) -> do
      let (cases, rest) = splitAt nCons casesrest
      cases' <- mapM (wrapMaybe . SystF.fromArg) cases
      return $ UnDestMeta n tyN tyArgs' x retTy cases' rest
    -- The fail string is being ignored by the 'MaybeT'; that's alright, they serve
    -- as programmer documentation or they can be plumbed through a 'trace' by
    -- overloading the MonadFail instance, which was helpful for debugging in the past.
    _ -> fail "unDest: Destructor arguments has non-cannonical structure"
unDest _ = fail "unDest: not an SystF.App"

data UnConsMeta lang meta = UnConsMeta
  { unconsTypeName :: TyName,
    unconsTypeArgs :: [TypeMeta lang meta],
    unconsIndex :: Int,
    unconsTermArgs :: [TermMeta lang meta]
  }

-- | Analogous to 'unDest', but works for constructors.
unCons :: (PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (UnConsMeta lang meta)
unCons (SystF.App (SystF.Free (TermSig n)) args) = do
  (idx, tyN) <- prtIsConst n
  let (tyArgs, args1) = span SystF.isTyArg args
  tyArgs' <- mapM (wrapMaybe . SystF.fromTyArg) tyArgs
  args1' <- mapM (wrapMaybe . SystF.fromArg) args1
  return $ UnConsMeta tyN tyArgs' idx args1'
-- The fail is meant for the 'MaybeT', check the comment in 'unDest' for rationale
unCons _ = fail "unCons: not an SystF.App"
