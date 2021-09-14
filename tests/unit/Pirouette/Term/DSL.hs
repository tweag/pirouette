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
import           Pirouette.Monad

import qualified PlutusCore        as P

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State ( modify )
import Data.Foldable (asum)
import Data.Maybe (fromJust)
import Data.List (elemIndex)
import qualified Data.Text as T
import qualified Data.Map as M

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

stubTy :: String -> PrtType
stubTy s = R.tyPure (R.F $ S.TyFree $ Name (T.pack s) Nothing)

type TestTerm = R.AnnTerm (R.AnnType Name (R.Var Name (TypeBase Name)))
                                Name
                                (R.Var Name (PIRBase P.DefaultFun Name))
type TermM = TermGenM TestTerm

term :: TermM -> PrtTerm
term gent = runReader gent []

class Abs t where
  lam_ann :: [(String, String)] -> t -> TermM

  lam :: String -> t -> TermM
  lam s = lam_ann (infinite (s,"stub"))
    where
      infinite :: a -> [a]
      infinite x = x : infinite x

instance Abs TermM where
  lam_ann _ = id

instance (Abs t) => Abs (TermM -> t) where
  lam_ann ((v,ty):tl) abst = do
    x <- mkNewName v
    R.Lam (R.Ann x) (stubTy ty) <$> local (x:) (lam_ann tl (abst (var x)))

lam1 :: (TermM -> TermM) -> TermM
lam1 = lam "x"

lam2 :: (TermM -> TermM -> TermM) -> TermM
lam2 = lam "x"

lam2_ann :: [(String, String)] -> (TermM -> TermM -> TermM) -> TermM
lam2_ann = lam_ann

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

func :: Name -> TermM
func n = return $ R.termPure (R.F $ S.FreeName n)

infix 4 .$
(.$) :: TermM -> TermM -> TermM
f .$ x = R.termApp <$> f <*> (R.Arg <$> x)

infix 4 .$$
(.$$) :: TermM -> [TermM] -> TermM
f .$$ xs = R.appN <$> f <*> (map R.Arg <$> sequence xs)

tyApp :: TermM -> Name -> TermM
tyApp t n = (`R.app` R.TyArg (R.tyPure $ R.F (S.TyFree n))) <$> t

infix 3 :->:
data PatternM where
  (:->:) :: (Abs a) => String -> a -> PatternM

caseofAnn :: String ->  String -> String -> TermM -> [PatternM] -> TermM
caseofAnn destr tyRes ty x pats = do
  cases <- mapM mklams pats
  x'    <- x
  return $ R.App (R.F $ S.FreeName $ Name (T.pack destr) Nothing)
                 (R.Arg x' : R.TyArg (stubTy tyRes) : map R.Arg cases)
  where
    mkHint ty constr = [head ty, head constr]
    mklams (constr :->: t) = lam (mkHint ty constr) t

caseof :: String -> TermM -> [PatternM] -> TermM
caseof ty = caseofAnn ("dest" ++ ty) "stub" ty

{-
declareDummyFunc :: (MonadPirouette m) => Name -> m ()
declareDummyFunc s =
  modify (\st -> st { decls = M.insert s dummyFun (decls st) })
  where
    dummyFun = S.DFunction S.Rec dummyTerm dummyType
    dummyTerm = R.termPure (R.F (S.FreeName "_"))
    dummyType = R.tyPure (R.F (S.TyFree "_"))
-}
