{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- |This module provides a straight forward DSL for building
-- 'Pirouette.Term.Syntax.Term', it is useful for tests.
module Pirouette.Term.DSL where

import           Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import qualified Pirouette.Term.Syntax as S

import qualified PlutusCore        as P

import Control.Monad.Reader
import Data.Foldable (asum)
import Data.Maybe (fromJust)
import Data.List (elemIndex)
import qualified Data.Text as T

type TermGenM = Reader [Name]

mkNewName :: String -> TermGenM Name
mkNewName c = do
  env <- ask
  return . fromJust . asum . map (notElem env)
    $ Name (T.pack c) Nothing : [ Name (T.pack c) (Just i) | i <- [0..]]
  where
    notElem env n
      | n `elem` env = Nothing
      | otherwise    = Just n

stub :: PirouetteType
stub = R.tyPure (R.F $ S.TyFree $ Name "stub" Nothing)

type TestTerm = R.AnnTerm (R.AnnType Name (R.Var Name (TypeBase Name)))
                                Name
                                (R.Var Name (PIRBase P.DefaultFun Name))
type TermM = TermGenM TestTerm

term :: TermM -> PirouetteTerm
term gent = runReader gent []

class Abs t where
  lam :: String -> t -> TermM

instance Abs TermM where
  lam _ = id

instance (Abs t) => Abs (TermM -> t) where
  lam hint abst = do
    x <- mkNewName hint
    R.Lam (R.Ann x) stub <$> local (x:) (lam hint (abst (var x)))

lam1 :: (TermM -> TermM) -> TermM
lam1 = lam "x"

lam2 :: (TermM -> TermM -> TermM) -> TermM
lam2 = lam "x"

lam3 :: (TermM -> TermM -> TermM -> TermM) -> TermM
lam3 = lam "x"

var :: Name -> TermM
var n = do
  stack <- ask
  case n `elemIndex` stack of
    Just i  -> return (R.termPure (R.B (R.Ann n) $ toInteger i))
    Nothing -> error $ "Undeclared variable " ++ show n

def :: Name -> TermM
def n = return $ R.App (R.F $ S.FreeName $ Name "def" Nothing)
               [R.Arg (R.termPure (R.F $ S.FreeName n))]

infix 4 .$
(.$) :: TermM -> TermM -> TermM
f .$ x = R.termApp <$> f <*> (R.Arg <$> x)

infix 4 .$$
(.$$) :: TermM -> [TermM] -> TermM
f .$$ xs = R.appN <$> f <*> (map R.Arg <$> sequence xs)

infix 3 :->:
data PatternM where
  (:->:) :: (Abs a) => String -> a -> PatternM

caseof :: String -> TermM -> [PatternM] -> TermM
caseof ty x pats = do
  cases <- mapM mklams pats
  x'    <- x
  return $ R.App (R.F $ S.FreeName $ Name (T.pack $ "dest" ++ ty) Nothing)
                 (R.Arg x' : R.TyArg stub : map R.Arg cases)
  where
    mkHint ty constr = [head ty, head constr]
    mklams (constr :->: t) = lam (mkHint ty constr) t
