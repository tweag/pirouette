{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Pirouette.Monad where

import           Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Monad.Logger
import           Pirouette.Monad.Maybe
import           Pirouette.Specializer.TypeDecl (TypeSpecializer)

import           PlutusCore (DefaultFun)
import           Control.Arrow (first, second)
import           Control.Monad
import           Control.Monad.Reader
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.State.Lazy   as Lazy
import           Control.Monad.Except
import           Control.Monad.Fail
import           Control.Monad.Identity
import           Data.Maybe
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as S
import           Data.Generics.Uniplate.Operations
import           Data.List.NonEmpty (NonEmpty(..))

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

-- |The error codes that pirouete can raise
data PrtError
  = PENotAType Name
  | PENotATerm Name
  | PEUndefined Name
  | PEMutRecDeps [Name]
  | PEOther String
  deriving (Eq, Show)

-- |And the actual error raised by the error monad. Make sure to raise these
-- with 'throwError'', so you can get the logger context in your error messages
-- for free.
data PrtErrorCtx = PrtErrorCtx
  { logCtx  :: [String]
  , message :: PrtError
  } deriving (Eq, Show)

-- |The base monadic layer we use in most places.
type PirouetteBase m = (MonadError PrtErrorCtx m, MonadLogger m, MonadFail m)

-- |'throwError' variant that automatically gets the logger context.
throwError' :: (PirouetteBase m) => PrtError -> m a
throwError' msg = do
  err <- flip PrtErrorCtx msg <$> context
  throwError err

-- ** Pirouette Definitions

-- |Whenever we need access to the list of definitions in the current PIR program
-- being compiled, we probably want to use 'PirouetteReadDefs' instead of 'PirouetteBase'
class (LanguageBuiltins lang, PirouetteBase m) => PirouetteReadDefs lang m | m -> lang where
  -- |Returns all declarations in scope
  prtAllDefs :: m (M.Map Name (Definition lang))

  -- |Returns the main program
  prtMain :: m (Term lang)

  -- |Returns the definition associated with a given name. Raises a 'PEUndefined'
  -- if the name doesn't exist.
  prtDefOf :: Name -> m (Definition lang)
  prtDefOf n = do
    defs <- prtAllDefs
    case M.lookup n defs of
      Nothing -> throwError' $ PEUndefined n
      Just x  -> return x

  prtTypeDefOf :: Name -> m (TypeDef lang)
  prtTypeDefOf n = prtDefOf n >>= maybe (throwError' $ PENotAType n) return . fromTypeDef

  prtTermDefOf :: Name -> m (Term lang)
  prtTermDefOf n = prtDefOf n >>= maybe (throwError' $ PENotATerm n) return . fromTermDef

  prtIsDest :: Name -> MaybeT m TyName
  prtIsDest n = MaybeT $ fromDestDef <$> prtDefOf n

  prtIsConst :: Name -> MaybeT m (Int , TyName)
  prtIsConst n = MaybeT $ fromConstDef <$> prtDefOf n

instance {-# OVERLAPPABLE #-} (PirouetteReadDefs lang m) => PirouetteReadDefs lang (Lazy.StateT s m) where
  prtAllDefs = lift prtAllDefs
  prtMain    = lift prtMain

instance {-# OVERLAPPABLE #-} (PirouetteReadDefs lang m) => PirouetteReadDefs lang (Strict.StateT s m) where
  prtAllDefs = lift prtAllDefs
  prtMain    = lift prtMain

-- |Given a prefix, if there is a single declared name with the given
-- prefix, returns it. Throws an error otherwise.
nameForPrefix :: (PirouetteReadDefs lang m) => T.Text -> m Name
nameForPrefix pref = pushCtx "nameForPrefix" $ do
  decls <- prtAllDefs
  let d = M.toList $ M.filterWithKey (\k _ -> pref `T.isPrefixOf` nameString k) decls
  case d of
    []      -> throwError' $ PEOther $ "No declaration with prefix: " ++ T.unpack pref
    [(n,_)] -> return n
    _       -> do
      logWarn $ "Too many declarations with prefix: " ++ T.unpack pref ++ ": " ++ show (map fst d)
      logWarn   "  will return the first one"
      return $ fst $ head d

-- |Returns the type of an identifier
typeOfIdent :: (PirouetteReadDefs lang m) => Name -> m (Type lang)
typeOfIdent n = do
  dn <- prtDefOf n
  case dn of
    (DFunction _ _ ty) -> return ty
    (DConstructor i t) -> snd . (!! i) . constructors <$> prtTypeDefOf t
    (DDestructor t)    -> destructorTypeFor <$> prtTypeDefOf t
    (DTypeDef _)       -> throwError' $ PEOther $ show n ++ " is a type"

-- |Returns the direct dependencies of a term. This is never cached and
-- is computed freshly everytime its called. Say we call @directDepsOf "f"@,
-- for:
--
-- > f x = g x + h
-- > g x = f (x - 1)
--
-- We'll get @S.fromList [R.Arg "g", R.Arg "h"]@. If you'd expect to see
-- @R.Arg "f"@ in the result aswell, use "Pirouette.Term.TransitiveDeps.transitiveDepsOf" instead.
directDepsOf :: (PirouetteReadDefs lang m) => Name -> m (S.Set (R.Arg Name Name))
directDepsOf n = do
  ndef <- prtDefOf n
  return $ case ndef of
    DFunction _ t ty -> typeNames ty <> termNames t
    DTypeDef d       -> S.unions (flip map (constructors d) $ \(n, c)
                                   -> S.unions $ map typeNames (fst $ R.tyFunArgs c))
    DConstructor  _ tyN -> S.singleton $ R.TyArg tyN
    DDestructor   tyN   -> S.singleton $ R.TyArg tyN

-- |Just like 'directDepsOf', but forgets the information of whether certain dependency
-- was on a type or a term.
directDepsOf' :: (PirouetteReadDefs lang m) => Name -> m (S.Set Name)
directDepsOf' = fmap (S.map (R.argElim id id)) . directDepsOf

-- |Returns whether a constructor is recursive. For the
-- type of lists, for example, @Cons@ would be recursive
-- whereas @Nil@ would not.
consIsRecursive :: (PirouetteReadDefs lang m) => TyName -> Name -> m Bool
consIsRecursive ty con = do
  conArgs <- fst . R.tyFunArgs <$> typeOfIdent con
  return $ any (\a -> R.TyArg ty `S.member` typeNames a) conArgs

-- |Returns whether a term definition uses itself directly, that is, for
--
-- > f x = g x + h
-- > g x = f (x - 1)
--
-- calling @termIsRecursive "f"@ would return @False@. See 'transitiveDepsOf' if
-- you want to know whether a term is depends on itself transitively.
termIsRecursive :: (PirouetteReadDefs lang m) => Name -> m Bool
termIsRecursive n = S.member (R.TermArg n) <$> directDepsOf n

-- *** Implementations for 'PirouetteReadDefs'

-- |Unordered definitions consist in a map of 'Name' to 'PrtDef' and
-- a /main/ term.
data PrtUnorderedDefs lang = PrtUnorderedDefs
  { prtUODecls    :: Decls lang
  , prtUOMainTerm :: Term lang
  }

instance (LanguageBuiltins lang, PirouetteBase m) => PirouetteReadDefs lang (ReaderT (PrtUnorderedDefs lang) m) where
  prtAllDefs = asks prtUODecls
  prtMain    = asks prtUOMainTerm

instance {-# OVERLAPPING #-} (LanguageBuiltins lang, PirouetteBase m)
    => PirouetteReadDefs lang (Strict.StateT (PrtUnorderedDefs lang) m) where
  prtAllDefs = Strict.gets prtUODecls
  prtMain    = Strict.gets prtUOMainTerm

-- |In contrast to ordered definitions, where we have a dependency order
-- for all term and type declarations in 'prtDecls'. That is, given two
-- terms @f@ and @g@, @f@ depends on @g@ if @elemIndex f prtDepOrder > elemIndex g prtDepOrder@,
-- that is, @f@ appears before @g@ in @prtDepOrder@.
data PrtOrderedDefs lang = PrtOrderedDefs
  { prtDecls    :: Decls lang
  , prtDepOrder :: [R.Arg Name Name]
  , prtMainTerm :: Term lang
  }

prtOrderedDefs :: PrtUnorderedDefs lang -> [R.Arg Name Name] -> PrtOrderedDefs lang
prtOrderedDefs uod ord = PrtOrderedDefs (prtUODecls uod) ord (prtUOMainTerm uod)

instance (LanguageBuiltins lang, PirouetteBase m) => PirouetteReadDefs lang (ReaderT (PrtOrderedDefs lang) m) where
  prtAllDefs = asks prtDecls
  prtMain    = asks prtMainTerm

class (PirouetteReadDefs lang m) => PirouetteDepOrder lang m where
  -- |Returns the dependency ordering of the currently declared terms.
  prtDependencyOrder :: m [R.Arg Name Name]

instance (LanguageBuiltins lang, PirouetteBase m) => PirouetteDepOrder lang (ReaderT (PrtOrderedDefs lang) m) where
  prtDependencyOrder = asks prtDepOrder

-- ** A 'PirouetteBase' Implementation:

-- |Read-only internal options
data PrtOpts = PrtOpts
  { logLevel :: LogLevel
  , logFocus :: [String]
  } deriving (Show)

newtype PrtT m a = PrtT
  { unPirouette :: ReaderT PrtOpts (ExceptT PrtErrorCtx (LoggerT m)) a }
  deriving newtype ( Functor, Applicative, Monad
                   , MonadError PrtErrorCtx, MonadReader PrtOpts
                   , MonadIO
                   )

instance (Monad m) => MonadLogger (PrtT m) where
  logMsg lvl msg = PrtT $ do
    l     <- asks logLevel
    focus <- asks logFocus
    ctx   <- lift $ lift context
    when (lvl >= l && isFocused ctx focus)
         (lift . lift . logMsg lvl $ msg)
    where
      isFocused ctx []    = True
      isFocused ctx focus = any (`elem` focus) ctx

  context     = PrtT $ lift $ lift context
  pushCtx ctx = PrtT . mapReaderT (mapExceptT $ pushCtx ctx) . unPirouette

instance (Monad m) => MonadFail (PrtT m) where
  fail msg = throwError' (PEOther msg)

-- |Runs a 'PrtT' computation, ignoring the resulting state
runPrtT :: (Monad m) => PrtOpts -> PrtT m a
                     -> m (Either PrtErrorCtx a, [LogMessage])
runPrtT opts = runLoggerT . runExceptT . flip runReaderT opts . unPirouette

-- |Mocks a 'PrtT' computation, running it with default options, omitting any logging
-- and displaying errors as strings already.
mockPrtT :: (Monad m) => PrtT m a -> m (Either String a, [LogMessage])
mockPrtT f = first (either (Left . show) Right) <$> runPrtT opts f
  where
    opts = PrtOpts TRACE []

-- |Pure variant of 'mockPrtT', over the Identity monad
mockPrt :: PrtT Identity a -> Either String a
mockPrt = fst . runIdentity . mockPrtT

-- |If we have a 'MonadIO' in our stack, we can ask for all the logs produced so far.
-- This is useful for the main function, to output the logs of different stages as these stages
-- complte.
--
-- If you have to add a @(MonadIO m) => ...@ constraint in order to use 'flushLogs' please
-- think three times. Often you can get by with using @Debug.Trace@ and not polluting the
-- code with unecesary IO.
flushLogs :: (MonadIO m) => PrtT m a -> PrtT m a
flushLogs = PrtT . mapReaderT (mapExceptT flushLogger) . unPirouette

-- * Some useful syntactical utilities

-- |A destructor application has the following form:
--
-- > [d/Type tyArg0 ... tyArgN X ReturnType case0 ... caseK extra0 ... extraL]
--
-- The 'unDest' function splits it up into:
--
-- > Just (d/Type, [tyArg0 .. tyArgN], X, ReturnType, [case0 .. caseK], [extra0 .. extraL])
--
-- Moreover, we already remove the 'R.Arg' wrapper for all the predefined argument positions.
-- Only the extra arguments are kept with their 'R.Arg' because they could be types or terms.
data UnDestMeta lang meta = UnDestMeta
  { undestName :: Name
  , undestTypeName :: TyName
  , undestTypeArgs :: [TypeMeta lang meta]
  , undestDestructed :: TermMeta lang meta
  , undestReturnType :: TypeMeta lang meta
  , undestCases :: [TermMeta lang meta]
  , undestCasesExtra :: [ArgMeta lang meta]
  }

unDest :: (PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (UnDestMeta lang meta)
unDest (R.App (R.Free (TermFromSignature n)) args) = do
  tyN <- prtIsDest n
  Datatype _ _ _ cons <- lift (prtTypeDefOf tyN)
  let nCons = length cons
  let (tyArgs, args1) = span R.isTyArg args
  tyArgs' <- mapM (wrapMaybe . R.fromTyArg) tyArgs
  case args1 of
    (R.TermArg x : R.TyArg retTy : casesrest) -> do
      let (cases, rest) = splitAt nCons casesrest
      cases' <- mapM (wrapMaybe . R.fromArg) cases
      return $ UnDestMeta n tyN tyArgs' x retTy cases' rest
    -- The fail string is being ignored by the 'MaybeT'; that's alright, they serve
    -- as programmer documentation or they can be plumbed through a 'trace' by
    -- overloading the MonadFail instance, which was helpful for debugging in the past.
    _ -> fail "unDest: Destructor arguments has non-cannonical structure"
unDest _ = fail "unDest: not an R.App"

data UnConsMeta lang meta = UnConsMeta
  { unconsTypeName :: TyName
  , unconsTypeArgs :: [TypeMeta lang meta]
  , unconsIndex :: Int
  , unconsTermArgs :: [TermMeta lang meta]
  }

-- |Analogous to 'unDest', but works for constructors.
unCons :: (PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (UnConsMeta lang meta)
unCons (R.App (R.Free (TermFromSignature n)) args) = do
  (idx, tyN) <- prtIsConst n
  let (tyArgs, args1) = span R.isTyArg args
  tyArgs' <- mapM (wrapMaybe . R.fromTyArg) tyArgs
  args1'  <- mapM (wrapMaybe . R.fromArg) args1
  return $ UnConsMeta tyN tyArgs' idx args1'
-- The fail is meant for the 'MaybeT', check the comment in 'unDest' for rationale
unCons _ = fail "unCons: not an R.App"
