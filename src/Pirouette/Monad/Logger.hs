{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE OverloadedStrings          #-}
module Pirouette.Monad.Logger where

import Pirouette.Monad.Maybe

import           Control.Arrow (second)
import           Control.Monad.Reader
import qualified Control.Monad.State.Lazy    as Lazy
import qualified Control.Monad.State.Strict  as Strict
import           Control.Monad.Writer.Strict
import           Control.Monad.Except
import           Data.List (intercalate)
import           Data.Foldable (toList)
import           Data.Sequence hiding (null)
import qualified ListT

data LogLevel = TRACE | DEBUG | INFO | WARN | ERROR | CRIT
  deriving (Eq, Show, Ord)

prettyLogLevel :: LogLevel -> String
prettyLogLevel TRACE = "TRCE"
prettyLogLevel DEBUG = "DEBG"
prettyLogLevel INFO  = "INFO"
prettyLogLevel WARN  = "WARN"
prettyLogLevel ERROR = "ERRO"
prettyLogLevel CRIT  = "CRIT"

data LogMessage = LogMessage
  { msgLevel   :: !LogLevel
  , msgContext :: ![String]
  , msgContent :: String -- we deliberately want to avoid forcing the computation
                         -- of the body, since the filter might skip it altogether.
  } deriving (Show)

printLogMessage :: (MonadIO m) => LogMessage -> m ()
printLogMessage (LogMessage lvl ctx body) =
  let line = concat [ "[" , prettyLogLevel lvl , "] "
                    , if null ctx
                      then ""
                      else intercalate "." ctx
                    , ": "
                    , body
                    ]
   in liftIO $ putStrLn line

type LogMessages = Seq LogMessage

class (Monad m) => MonadLogger m where
  logMsg  :: LogLevel -> String -> m ()
  pushCtx :: String -> m a -> m a
  context :: m [String]

  logTrace :: String -> m ()
  logTrace = logMsg TRACE

  logDebug :: String -> m ()
  logDebug = logMsg DEBUG

  logInfo  :: String -> m ()
  logInfo  = logMsg INFO

  logWarn  :: String -> m ()
  logWarn  = logMsg WARN

  logError  :: String -> m ()
  logError  = logMsg ERROR

newtype LoggerT m a = LoggerT { unLogger :: WriterT LogMessages (ReaderT [String] m) a }
  deriving newtype (Functor, Applicative, Monad, MonadIO)

mapLoggerT :: (m (a, LogMessages) -> n (a, LogMessages))
           -> LoggerT m a -> LoggerT n a
mapLoggerT f = LoggerT . mapWriterT (mapReaderT f) . unLogger

runLoggerT :: (Monad m) => LoggerT m a -> m (a, [LogMessage])
runLoggerT = fmap (second toList) . flip runReaderT mempty . runWriterT . unLogger

flushLogger :: (MonadIO m) => LoggerT m a -> LoggerT m a
flushLogger = LoggerT . mapWriterT (mapReaderT go) . unLogger
  where
    go m = do
      (a, msgs) <- m
      mapM_ printLogMessage (toList msgs)
      return (a, mempty)

instance MonadTrans LoggerT where
  lift = LoggerT . lift . lift

instance (Monad m) => MonadLogger (LoggerT m) where
  logMsg lvl m = LoggerT $ do
    ctx <- ask
    tell (singleton $ LogMessage lvl ctx m)
  pushCtx ctx  = LoggerT . local (ctx:) . unLogger
  context      = LoggerT ask

instance (MonadLogger m) => MonadLogger (MaybeT m) where
  logMsg lvl m = lift $ logMsg lvl m
  pushCtx ctx  = MaybeT . pushCtx ctx . runMaybeT
  context      = lift context

instance (MonadLogger m) => MonadLogger (ReaderT r m) where
  logMsg lvl m = lift $ logMsg lvl m
  pushCtx ctx  = mapReaderT (pushCtx ctx)
  context      = lift context

instance (MonadLogger m) => MonadLogger (Lazy.StateT s m) where
  logMsg lvl m = lift $ logMsg lvl m
  pushCtx ctx  = Lazy.mapStateT (pushCtx ctx)
  context      = lift context

instance (MonadLogger m) => MonadLogger (Strict.StateT s m) where
  logMsg lvl m = lift $ logMsg lvl m
  pushCtx ctx  = Strict.mapStateT (pushCtx ctx)
  context      = lift context

instance (MonadLogger m) => MonadLogger (ListT.ListT m) where
  logMsg lvl m = lift $ logMsg lvl m
  pushCtx ctx (ListT.ListT m) = ListT.ListT $ pushCtx ctx m
  context = lift context
