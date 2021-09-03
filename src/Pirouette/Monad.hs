{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import           Control.Monad.State.Strict
import           Control.Monad.Except
import           Control.Monad.Fail
import           Control.Monad.Identity
import           Data.Maybe
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as S
import           Data.Generics.Uniplate.Operations
import           Data.List.NonEmpty (NonEmpty(..))

-- * The Pirouette Monad
--
-- $pirouettemonad
--
-- The pirouette monad provides us with all the relevant type-checking functionality
-- for our translation into TLA.

-- TODO: We keep the `deps` var below in order to memoize the dependencies of
--       terms and avoid recomputing these all the time. Yet, we have transformations
--       that change the definition of terms in decls. We should stop and think about
--       adding a function to invalidate the `deps` cache and think carefully about where
--       to use it. One option would be to keep a flag and set it to true whenever we
--       modify decls.

-- |The compiler state consists in:
data PrtState = PrtState
  { decls :: Decls Name DefaultFun -- ^ All the declarations in scope
  , prog  :: PrtTerm -- ^ Main program
  , deps  :: M.Map Name (S.Set (R.Arg Name Name)) -- ^ cache for fast 'transitiveDepsOf'
  , tord  :: Maybe [R.Arg Name Name] -- ^ Dependency order of declarations; 'elimEvenOddMutRec' sets this to @Just@ upon success.
  }

-- |Read-only options
data PrtOpts = PrtOpts
  { logLevel :: LogLevel
  , logFocus :: [String]
  } deriving (Show)

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

-- |Pirouette functionality
class ( MonadLogger m, MonadState PrtState m, MonadError PrtErrorCtx m
      , MonadReader PrtOpts m, MonadFail m)
 => MonadPirouette m where
  -- |Returns the definition associated with a given name. Raises a 'PEUndefined'
  -- if the name doesn't exist.
  defOf :: Name -> m PrtDef

  -- |Returns the type and term-level transitive dependencies associated with a name,
  -- memoizes the result for future queries.
  --
  -- /WARNING:/ if you change the definitions
  -- of some terms you might see the wrong dependencies since 'depsOf' will return
  -- whatever it had in its memoized cache before the changes to the definitions.
  transitiveDepsOf :: Name -> m (S.Set (R.Arg Name Name))

  typeDefOf :: Name -> m PrtTypeDef
  typeDefOf n = defOf n >>= maybe (throwError' $ PENotAType n) return . fromTypeDef

  termDefOf :: Name -> m PrtTerm
  termDefOf n = defOf n >>= maybe (throwError' $ PENotATerm n) return . fromTermDef

  isDest :: Name -> MaybeT m TyName
  isDest n = MaybeT $ fromDestDef <$> defOf n

  isConst :: Name -> MaybeT m (Int , TyName)
  isConst n = MaybeT $ fromConstDef <$> defOf n

-- |Returns the order of dependencies for the current session if we have one available.
-- Computing such order can be done with 'elimEvenOddMutRec'.
--
-- TODO: This is brittle and an unnecessary error. At some point I'd like to split
-- the MonadPirouette into different stages; 'dependencyOrder' should only be available
-- after the /sorting dependencies/ stage happens.
dependencyOrder :: (MonadPirouette m) => m [R.Arg Name Name]
dependencyOrder = do
  mdeps <- gets tord
  maybe (throwError' $ PEOther "No dependency order computed.") return mdeps

-- |Modifyes or deletes an existing definition. Will also remove said name from
-- the cache of transitive dependencies.
modifyDef :: (MonadPirouette m) => Name -> (PrtDef -> Maybe PrtDef) -> m ()
modifyDef n f = modify $ \st ->
  st { decls = M.alter (>>= f) n (decls st)
     , deps  = M.delete n (deps st)
     }

-- |Given a prefix, if there is a single declared name with the given
-- prefix, returns it. Throws an error otherwise.
nameForPrefix :: (MonadPirouette m) => T.Text -> m Name
nameForPrefix pref = pushCtx "nameForPrefix" $ do
  decls <- gets decls
  let d = M.toList $ M.filterWithKey (\k _ -> pref `T.isPrefixOf` nameString k) decls
  case d of
    []      -> throwError' $ PEOther $ "No declaration with prefix: " ++ T.unpack pref
    [(n,_)] -> return n
    _       -> do
      logWarn $ "Too many declarations with prefix: " ++ T.unpack pref ++ ": " ++ show (map fst d)
      logWarn   "  will return the first one"
      return $ fst $ head d

-- |Returns the type of an identifier
typeOfIdent :: (MonadPirouette m) => Name -> m PrtType
typeOfIdent n = do
  dn <- defOf n
  case dn of
    (DFunction _ _ ty) -> return ty
    (DConstructor i t) -> snd . (!! i) . constructors <$> typeDefOf t
    (DDestructor t)    -> destructorTypeFor <$> typeDefOf t
    (DTypeDef _)       -> throwError' $ PEOther $ show n ++ " is a type"

-- ** Dependency Management

-- |Returns all the dependencies of a name ignoring whether they are types or terms.
transitiveDepsOf' :: (MonadPirouette m) => Name -> m (S.Set Name)
transitiveDepsOf' = fmap (S.map (R.argElim id id)) . transitiveDepsOf

-- |Returns whether a constructor is recursive. For the
-- type of lists, for example, @Cons@ would be recursive
-- whereas @Nil@ would not.
consIsRecursive :: (MonadPirouette m) => TyName -> Name -> m Bool
consIsRecursive ty con = do
  conArgs <- fst . R.tyFunArgs <$> typeOfIdent con
  return $ any (\a -> R.TyArg ty `S.member` typeNames a) conArgs

-- |Returns the direct dependencies of a term. This is never cached and
-- is computed freshly everytime its called. Say we call @directDepsOf "f"@,
-- for:
--
-- > f x = g x + h
-- > g x = f (x - 1)
--
-- We'll get @S.fromList [R.Arg "g", R.Arg "h"]@. If you'd expect to see
-- @R.Arg "f"@ in the result aswell, use 'transitiveDepsOf' instead.
directDepsOf :: (MonadPirouette m) => Name -> m (S.Set (R.Arg Name Name))
directDepsOf n = do
  ndef <- defOf n
  return $ case ndef of
    DFunction _ t ty -> typeNames ty <> termNames t
    DTypeDef d       -> S.unions (flip map (constructors d) $ \(n, c)
                                   -> S.unions $ map typeNames (fst $ R.tyFunArgs c))
    DConstructor  _ tyN -> S.singleton $ R.TyArg tyN
    DDestructor   tyN   -> S.singleton $ R.TyArg tyN

-- |Just like 'directDepsOf', but forgets the information of whether certain dependency
-- was on a type or a term.
directDepsOf' :: (MonadPirouette m) => Name -> m (S.Set Name)
directDepsOf' = fmap (S.map (R.argElim id id)) . directDepsOf

-- |Returns whether a term definition uses itself directly, that is, for
--
-- > f x = g x + h
-- > g x = f (x - 1)
--
-- calling @termIsRecursive "f"@ would return @False@. See 'transitiveDepsOf' if
-- you want to know whether a term is depends on itself transitively.
termIsRecursive :: (MonadPirouette m) => Name -> m Bool
termIsRecursive n = S.member (R.Arg n) <$> directDepsOf n

-- |Given a list of names, sort them according to their dependencies.
sortDeps :: (MonadPirouette m) => [R.Arg Name Name] -> m [NonEmpty (R.Arg Name Name)]
sortDeps = equivClassesM (\x d -> S.member x <$> transitiveDepsOf (R.argElim id id d))

-- *** Utility Functions

partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f []     = return ([], [])
partitionM f (x:xs) = f x >>= (<$> partitionM f xs) . ite (first (x:)) (second (x:))
  where ite t e True  = t
        ite t e False = e

-- |Given a preorder relation @depM@, 'equivClassesM' computes
-- the equivalence classes of @depM@, on @xs@ such that if
--
-- > equivClassesM depOn xs == [r0, ..., rN]
--
-- Then each @m, n@ in @ri@ for some @i@ is mutually dependent @depOn m n && depOn n m@
-- and if there exists @m@ in @ri@ and @n@ in @rj@, then @i >= j@ iff @depOn m n@.
equivClassesM :: (Monad m) => (a -> a -> m Bool) -> [a] -> m [NonEmpty a]
equivClassesM depM []     = return []
equivClassesM depM (d:ds) = do
  -- we start by splitting the dependencies of d from the rest,
  (depsOfD, aft)  <- partitionM (depM d) ds
  -- Now, out the dependencies of d, we split off those that depend on d itself.
  (eq, bef)       <- partitionM (`depM` d) depsOfD
  bef'            <- equivClassesM depM bef
  aft'            <- equivClassesM depM aft
  return $ bef' ++ ( [d :| eq] ++ aft' )

-- Non-monadic version of 'equivClassesM'; useful for testing
-- equivClasses :: (a -> a -> Bool) -> [a] -> [NonEmpty a]
-- equivClasses leq = runIdentity . equivClassesM (\a -> return . leq a)

-- ** A MonadPirouette Implementation:

-- TODO: maybe pull the except monad to the top; we'd want to get the resulting
-- state even in case of an error.
newtype PrtT m a = PrtT
  { unPirouette :: StateT PrtState (ReaderT PrtOpts (ExceptT PrtErrorCtx (LoggerT m))) a }
  deriving newtype ( Functor, Applicative, Monad
                   , MonadError PrtErrorCtx, MonadState PrtState, MonadReader PrtOpts
                   , MonadIO
                   )

throwError' :: (MonadError PrtErrorCtx m, MonadLogger m) => PrtError -> m a
throwError' msg = do
  err <- flip PrtErrorCtx msg <$> context
  throwError err

instance (Monad m) => MonadPirouette (PrtT m) where
  defOf  n = gets (M.lookup n . decls) >>= maybe (throwError' $ PEUndefined n) return

  transitiveDepsOf n = pushCtx ("transitiveDepsOf " ++ show n) $ go S.empty n
    where
      go :: (Monad m) => S.Set Name -> Name -> PrtT m (S.Set (R.Arg Name Name))
      go stack n = do
        mr <- gets (M.lookup n . deps)
        case mr of
          Just ds -> return ds
          Nothing -> do
            r <- computeDeps stack n
            modify (\st -> st { deps = M.insert n r (deps st) })
            return r

      computeDeps stack n
        | n `S.member` stack = return S.empty
        | otherwise = do
          deps0 <- directDepsOf n
          let stack' = S.insert n stack
          let deps1  = S.map (R.argElim id id) deps0
          S.unions . (deps0 :) <$> mapM (go stack') (S.toList deps1)

instance (Monad m) => MonadLogger (PrtT m) where
  logMsg lvl msg = PrtT $ do
    l     <- asks logLevel
    focus <- asks logFocus
    ctx   <- lift $ lift $ lift context
    when (lvl >= l && isFocused ctx focus)
         (lift . lift . lift . logMsg lvl $ msg)
    where
      isFocused ctx []    = True
      isFocused ctx focus = any (`elem` focus) ctx

  context     = PrtT $ lift $ lift $ lift context
  pushCtx ctx = PrtT . mapStateT (mapReaderT . mapExceptT $ pushCtx ctx) . unPirouette

instance (Monad m) => MonadFail (PrtT m) where
  fail msg = throwError' (PEOther msg)

-- |Runs a 'PrtT' computation, ignoring the resulting state
runPrtT :: (Monad m) => PrtOpts -> PrtState -> PrtT m a
                     -> m (Either PrtErrorCtx a, [LogMessage])
runPrtT opts st = runLoggerT . runExceptT . flip runReaderT opts . flip evalStateT st . unPirouette

-- |Mocks a 'PrtT' computation, running it with default options, omitting any logging
-- and displaying errors as strings already.
mockPrtT :: (Monad m) => Decls Name DefaultFun -> PrtT m a -> m (Either String a)
mockPrtT ds f = either (Left . show) Right . fst <$> runPrtT opts st f
  where
    st   = PrtState ds (error "mockPrtT has no main program") M.empty Nothing
    opts = PrtOpts CRIT []

-- |Pure variant of 'mockPrtT', over the Identity monad
mockPrt :: Decls Name DefaultFun -> PrtT Identity a -> Either String a
mockPrt ds = runIdentity . mockPrtT ds

-- |If we have a 'MonadIO' in our stack, we can ask for all the logs produced so far.
-- This is useful for the main function, to output the logs of different stages as these stages
-- complte.
--
-- If you have to add a @(MonadIO m) => ...@ constraint in order to use 'flushLogs' please
-- think three times. Often you can get by with using @Debug.Trace@ and not polluting the
-- code with unecesary IO.
flushLogs :: (MonadIO m) => PrtT m a -> PrtT m a
flushLogs = PrtT . mapStateT (mapReaderT . mapExceptT $ flushLogger) . unPirouette
