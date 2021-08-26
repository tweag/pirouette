{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE FlexibleContexts     #-}

module Pirouette.Pipeline where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.String.Interpolate

type TransformLog = [String]

postprocLog :: TransformLog -> [String]
postprocLog = reverse

-- This will eventually be moved out into a separate library
ifEnabled :: (MonadReader env m, MonadWriter TransformLog m, Show a)
          => String
          -> (env -> Bool)
          -> (a -> a)
          -> a
          -> m a
ifEnabled ctx cond f arg = do
  val <- asks cond
  if val
    then do let result = f arg
            tell $ pure [i|#{ctx}: #{result}|]
            pure result
    else do tell $ pure [i|#{ctx}: skipping |]
            pure arg

ifSpecifiedA :: (Applicative f, MonadReader env m, MonadWriter TransformLog m, Show (f a))
             => String
             -> (env -> Maybe opt)
             -> (opt -> a -> f a)
             -> a
             -> m (f a)
ifSpecifiedA ctx optGetter f arg = do
  opt <- asks optGetter
  case opt of
       Just optVal -> do let result = f optVal arg
                         tell $ pure [i|#{ctx}: #{result}|]
                         pure result
       Nothing -> do tell $ pure [i|#{ctx}: skipping|]
                     pure $ pure arg

ifSpecifiedM :: (MonadReader env m, MonadWriter TransformLog m, Show a)
             => String
             -> (env -> Maybe opt)
             -> (opt -> a -> m a)
             -> a
             -> m a
ifSpecifiedM ctx optGetter f arg = do
  opt <- asks optGetter
  case opt of
       Just optVal -> do result <- f optVal arg
                         tell $ pure [i|#{ctx}: #{result}|]
                         pure result
       Nothing -> do tell $ pure [i|#{ctx}: skipping|]
                     pure arg

ifSpecified :: (MonadReader env m, MonadWriter TransformLog m, Show a)
            => String
            -> (env -> Maybe opt)
            -> (opt -> a -> a)
            -> a
            -> m a
ifSpecified ctx optGetter f arg = runIdentity <$> ifSpecifiedA ctx optGetter (\opt -> pure . f opt) arg

always :: (MonadWriter TransformLog m, Show a) => String -> a -> m a
always ctx arg = do
  tell $ pure [i|#{ctx}: #{arg}|]
  pure arg

branchOn :: (MonadReader env m, MonadWriter TransformLog m, Show b)
         => String
         -> (env -> Bool)
         -> (a -> b)
         -> (a -> b)
         -> a
         -> m b
branchOn ctx cond ifTrue ifFalse arg = do
  val <- asks cond
  if val
    then do let result = ifTrue arg
            tell $ pure [i|#{ctx} is true: #{result}|]
            pure result
    else do let result = ifFalse arg
            tell $ pure [i|#{ctx} is false: #{result}|]
            pure result

