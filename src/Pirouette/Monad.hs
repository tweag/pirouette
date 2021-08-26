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

import           PlutusCore (DefaultFun)
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Except
import           Control.Monad.Fail
import           Data.Maybe
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as S
import           Data.Generics.Uniplate.Operations

-- * The Pirouette Monad
--
-- $pirouettemonad
--
-- The pirouette monad provides us with all the relevant type-checking functionality
-- for our translation into TLA.

-- |The compiler state consists in:
data PrtState = PrtState
  { decls :: Decls Name DefaultFun
  , deps  :: M.Map Name (S.Set (R.Arg Name Name))
  , prog  :: PrtTerm
  }

-- |Read-only options
data PrtOpts = PrtOpts
  { logLevel :: LogLevel
  , logFocus :: [String]
  } deriving (Show)

-- |Errors
--
-- TODO: make a more complex error structure and borrow the context from
--       the logger monad!
data PrtError
  = PENotAType Name
  | PENotATerm Name
  | PEUndefined Name
  | PEOther String
  deriving (Eq, Show)

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
  defOf     :: Name -> m PrtDef

  -- |Returns the type and term-level dependencies associated with a name,
  -- memoizes the result for future queries.
  depsOf    :: Name -> m (S.Set (R.Arg Name Name))

  typeDefOf :: Name -> m PrtTypeDef
  typeDefOf n = defOf n >>= maybe (throwError' $ PENotAType n) return . fromTypeDef

  termDefOf :: Name -> m PrtTerm
  termDefOf n = defOf n >>= maybe (throwError' $ PENotATerm n) return . fromTermDef

  isDest :: Name -> MaybeT m TyName
  isDest n = MaybeT $ fromDestDef <$> defOf n

  isConst :: Name -> MaybeT m (Int , TyName)
  isConst n = MaybeT $ fromConstDef <$> defOf n

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

-- |Returns whether a term depends on itself
termIsRecursive :: (MonadPirouette m) => Name -> m Bool
termIsRecursive n = S.member (R.Arg n) <$> depsOf n

-- |Returns whether a constructor is recursive. For the
-- type of lists, for example, @Cons@ would be recursive
-- whereas @Nil@ would not.
consIsRecursive :: (MonadPirouette m) => TyName -> Name -> m Bool
consIsRecursive ty con = do
  conArgs <- R.tyFunArgs <$> typeOfIdent con
  return $ any (\a -> R.TyArg ty `S.member` typeNames a) conArgs

-- |Returns the type of an identifier
typeOfIdent :: (MonadPirouette m) => Name -> m PrtType
typeOfIdent n = do
  dn <- defOf n
  case dn of
    (DFunction _ _ ty) -> return ty
    (DConstructor i t) -> snd . (!! i) . constructors <$> typeDefOf t
    (DDestructor t)    -> destructorTypeFor <$> typeDefOf t
    (DTypeDef _)       -> throwError' $ PEOther $ show n ++ " is a type"

-- |Definition Dependency Partial order
depsOnLT :: (MonadPirouette m) => Name -> Name -> m Bool
depsOnLT n m =
  let f x ds = R.Arg x `S.member` ds || R.TyArg x `S.member` ds
   in f n <$> depsOf m

depsOnAny :: (MonadPirouette m) => (a -> Name) -> Name -> [a] -> m Bool
depsOnAny f n ms = or <$> mapM (depsOnLT n . f) ms

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

  depsOf = pushCtx "depsOf" . go S.empty
    where
      go :: (Monad m) => S.Set Name -> Name -> PrtT m (S.Set (R.Arg Name Name))
      go stack n = do
        mr <- gets (M.lookup n . deps)
        case mr of
          Just ds -> return ds
          Nothing -> do
            r <- computeDeps stack n
            modify (\st -> st { deps = M.insert n r (deps st) })
            logTrace ("Dependencies For" ++ show n ++ " = " ++ show r)
            return r

      computeDeps stack n
        | n `S.member` stack = return S.empty
        | otherwise = do
          ndef  <- defOf n
          let deps0 = case ndef of
                DFunction _ t ty -> typeNames ty <> termNames t
                DTypeDef d       -> S.unions (flip map (constructors d) $ \(n, c)
                                               -> S.unions $ map typeNames (fst $ R.tyFunArgs c))
                DConstructor  _ tyN -> S.singleton $ R.TyArg tyN
                DDestructor   tyN   -> S.singleton $ R.TyArg tyN
          let stack' = S.insert n stack
          S.unions . (deps0 :) <$> mapM (R.argElim (go stack') (go stack')) (S.toList deps0)

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

runPrtT :: (Monad m)
           => PrtOpts -> PrtState -> PrtT m a
           -> m (Either PrtErrorCtx a, [LogMessage])
runPrtT opts st = runLoggerT . runExceptT . flip runReaderT opts . flip evalStateT st . unPirouette

flushLogs :: (MonadIO m) => PrtT m a -> PrtT m a
flushLogs = PrtT . mapStateT (mapReaderT . mapExceptT $ flushLogger) . unPirouette
