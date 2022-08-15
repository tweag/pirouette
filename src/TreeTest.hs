{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use foldr" #-}
module TreeTest where

import Control.Arrow (first, second)
import Control.Monad
import Data.Foldable
import Data.IORef
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
import Debug.Trace
import System.IO.Unsafe

----------------------------------------
-- Term type to symbolically execute: --
----------------------------------------

-- This term type was inspired by our own SystF.Term from Pirouette
data Term m
  = Lam String (Term m)
  | App (Var m) [Term m]
  deriving (Show, Functor)

data Var m
  = Bound String
  | Free String
  | Meta m
  | Bottom
  | ConsZero
  | ConsSucc
  | NatCase
  deriving (Show, Functor)

type Defs = M.Map String (Term Void)

type Meta = String

------------------------------------------------
-- Infinite trees, giving semantics to terms: --
------------------------------------------------

-- Look up: Bohm Trees
data TermSet
  = Union [TermSet]
  | Learn String TermSet
  | -- TODO: having the term structure is nice and all, but
    -- we never have any Lam in here at all; Maybe a dedicated @WHNFTerm@ datatype
    -- would be a little more interesting
    Spine (Term TermSet)
  | Call ([TermSet] -> TermSet) [TermSet]
  | Dest ((CotrInfo, [TermSet]) -> TermSet) TermSet
  | -- The maybe represent rigid versus flexible metavariables. Flexible metas
    -- are those that we can continue expanding ad-infinitum, for instance, imagine
    -- a meta @k@ of type @[Int]@, we can always expand @k = j : k'@, and continue
    -- expanding @k'@, but we can't expand @j@ since it's of a builtin type
    Inst Meta (Maybe TermSet)

-- Well, look... why not merge Call and Dest? Isn't 'Call' just the
-- destructor for functions?

-- It is important that it is possible to construct a termset with a single term on it.
tsSingleton :: Term Meta -> TermSet
tsSingleton = Spine . fmap (`Inst` Nothing)

instance Show TermSet where
  show (Inst m _) = "ts$" ++ show m
  show _ = "<ts>"

data CotrInfo = CIZero | CISucc | CIBottom
  deriving (Eq)

------

type ScopedTerm = (S.Set Meta, Term Meta)

type ScopedMeta = (S.Set Meta, Meta)

termVars :: Term m -> ([String], Term m)
termVars (Lam n t) = first (n :) $ termVars t
termVars t = ([], t)

-- The anamorphism!
symbolically :: Defs -> Term Void -> TermSet
symbolically defs = withSymVars
  where
    withSymVars :: Term Void -> TermSet
    withSymVars t =
      let vs = fst $ termVars t
       in Learn ("decl " ++ show vs) $
            evalChooseLoop (S.fromList vs, appN (termCast t) (map meta vs))

    evalChooseLoop :: ScopedTerm -> TermSet
    evalChooseLoop t = trace inf $ eval choose t
      where
        inf = "evalChooseLoop: " ++ show t

    eval :: ((S.Set Meta, m) -> TermSet) -> (S.Set Meta, Term m) -> TermSet
    eval _ (_, Lam {}) = error "Lam has no eval"
    eval f (s, App hd args) =
      case hd of
        ConsSucc -> Spine $ App ConsSucc $ map (meta . eval f . (s,)) args
        ConsZero -> Spine $ App ConsZero []
        Bottom -> Spine $ App Bottom []
        NatCase -> case args of
          [mot, cZ, cS] ->
            flip Dest (eval f (s, mot)) $ \case
              (CIZero, []) -> eval f (s, cZ)
              (CISucc, [x]) -> liftedApp' s (fmap (f . (s,)) cS) [x]
              _ -> error "type error"
          _ -> error "too little args to NatCase"
        Bound _ -> error "Bound head"
        Meta n -> f (s, n)
        Free n ->
          let bodyN = termCast $ defs M.! n
           in Call (liftedApp s bodyN) (map (eval f . (s,)) args)

    choose :: ScopedMeta -> TermSet
    choose (s, n) = Inst n $
      Just $
        Union $
          flip map [CIZero, CISucc] $ \cons ->
            let (vs, cotr) = mkSymbolicCotr cons
             in (if S.null vs then id else Learn ("decl " ++ show (S.toList vs) ++ "")) $
                  Learn (n ++ " == " ++ show cotr) $ eval choose (S.union s vs, cotr)

    -- Two slightly different versions of lifted application:

    liftedApp' :: S.Set Meta -> Term TermSet -> [TermSet] -> TermSet
    liftedApp' s body args =
      eval snd (s, either id id <$> genericApp body args)

    liftedApp :: S.Set Meta -> Term Meta -> [TermSet] -> TermSet
    liftedApp s body args =
      eval snd (s, either (choose . (s,)) id <$> genericApp body args)

    genericApp :: Term m -> [arg] -> Term (Either m arg)
    genericApp body args =
      let body' = fmap Left body
          args' = fmap (meta . Right) args
       in body' `appN` args'

mkSymbolicCotr :: CotrInfo -> (S.Set Meta, Term Meta)
mkSymbolicCotr CIZero = (S.empty, App ConsZero [])
mkSymbolicCotr t@CISucc =
  let v = "$s" ++ show (giveMeFresh t)
   in (S.singleton v, App ConsSucc [meta v])
mkSymbolicCotr _ = error "x"

------

data CallConvention
  = CallByName
  | CallByValue

type State = [String]

cata :: CallConvention -> Integer -> TermSet -> [(State, Term Meta)]
cata cc depth = go depth []
  where
    go :: Integer -> State -> TermSet -> [(State, Term Meta)]
    go n st ts = do
      (st', res) <- goWHNF n st ts
      case res of
        Left m -> return (st', App (Meta m) [])
        Right (ci, ts') ->
          case ci of
            CIBottom -> return (st', App Bottom [])
            CIZero -> return (st', App ConsZero [])
            CISucc -> do
              (sts, args) <- combineArgs st' <$> traverse (go (n - 1) st') ts'
              return (sts, App ConsSucc args)

    goWHNF :: Integer -> State -> TermSet -> [(State, Either Meta (CotrInfo, [TermSet]))]
    goWHNF n st (Learn s ts) = goWHNF (n - 1) (s : st) ts
    goWHNF n st (Union tss) = asum (map (goWHNF n st) tss)
    goWHNF n st (Inst m Nothing) = return (st, Left m)
    goWHNF n st (Inst m (Just ts))
      | n <= 0 = return (st, Left m)
      | otherwise = goWHNF (n - 1) st ts
    goWHNF n st (Call f args) =
      case cc of
        CallByName -> goWHNF n st (f args)
        CallByValue -> do
          (st', xs) <- combineArgs st <$> traverse (go n st) args
          if any isBottom xs
            then return (st', Right (CIBottom, []))
            else goWHNF n st' (f $ map tsSingleton xs)
    goWHNF n st (Dest f x) = do
      (st', res) <- goWHNF n st x
      case res of
        Left m -> [] -- can't match on meta
        Right (ci, ts) ->
          if ci == CIBottom
            then return (st', Right (ci, ts))
            else goWHNF (n - 1) st' (f (ci, ts))
    goWHNF n st (Spine t) =
      case t of
        Lam {} -> error "I won't return lams to you"
        App (Bound _) _ -> error "I won't return bounds to you"
        App (Free _) _ -> error "I won't return frees to you"
        App NatCase _ -> error "I won't return cases to you"
        App ConsZero args -> return (st, Right (CIZero, map Spine args))
        App ConsSucc args -> return (st, Right (CISucc, map Spine args))
        App Bottom args -> return (st, Right (CIBottom, []))
        App (Meta ts') (_ : _) -> error "I won't return an applied term set to you"
        App (Meta ts') [] -> goWHNF n st ts'

    combineArgs :: State -> [(State, a)] -> (State, [a])
    combineArgs s0 [] = (s0, [])
    combineArgs s0 xs = first concat . unzip $ xs

isBottom :: Term Meta -> Bool
isBottom (App Bottom _) = True
isBottom _ = False

cataIO :: CallConvention -> Integer -> TermSet -> IO ()
cataIO cc n t = mapM_ (uncurry pretty) $ cata cc n t
  where
    pretty strs res =
      putStrLn $ "- " ++ show res ++ "\n" ++ unlines (map ("    " ++) strs)

-----------------

-- add Zero m = m
-- add (Suc n) m = Suc (add (const n (error "blah")) m)
add :: (String, Term m)
add =
  ( "add",
    Lam "n" $
      Lam "m" $
        App
          NatCase
          [ bound "n",
            bound "m",
            Lam "sn" $
              App
                ConsSucc
                [ appN (free "add") [appN (free "const") [bound "sn", App Bottom []], bound "m"]
                ]
          ]
  )

constF :: (String, Term m)
constF = ("const", Lam "n" $ Lam "m" $ bound "n")

defs :: Defs
defs = M.fromList [add, constF]

go :: CallConvention -> Integer -> IO ()
go cc n =
  cataIO cc n $
    symbolically defs $ Lam "k" (appN (free "add") [bound "k", App ConsSucc [bound "k"]])

-- Boilerplate:

------

bottom :: Term m
bottom = App Bottom []

bound :: String -> Term m
bound s = App (Bound s) []

free :: String -> Term m
free s = App (Free s) []

meta :: m -> Term m
meta s = App (Meta s) []

termDistr :: (Applicative f) => Term (f a) -> f (Term a)
termDistr (App fa args) = App <$> varDistr fa <*> traverse termDistr args
termDistr (Lam s t) = Lam s <$> termDistr t

varDistr :: (Applicative f) => Var (f a) -> f (Var a)
varDistr (Bound s) = pure (Bound s)
varDistr (Free s) = pure (Free s)
varDistr Bottom = pure Bottom
varDistr NatCase = pure NatCase
varDistr ConsZero = pure ConsZero
varDistr ConsSucc = pure ConsSucc
varDistr (Meta s) = Meta <$> s

termStr :: Term (a, b) -> ([a], Term b)
termStr (App fa args) =
  let (a1, fa') = varStr fa
      (as, args') = unzip $ map termStr args
   in (a1 ++ concat as, App fa' args')
termStr (Lam s t) = second (Lam s) (termStr t)

varStr :: Var (a, b) -> ([a], Var b)
varStr (Bound s) = ([], Bound s)
varStr (Free s) = ([], Free s)
varStr Bottom = ([], Bottom)
varStr ConsZero = ([], ConsZero)
varStr ConsSucc = ([], ConsSucc)
varStr NatCase = ([], NatCase)
varStr (Meta (a, b)) = ([a], Meta b)

termJoin :: Term (Term a) -> Term a
termJoin (App (Meta m) args) = appN m (map termJoin args)
termJoin (App (Bound s) args) = App (Bound s) (map termJoin args)
termJoin (App (Free s) args) = App (Free s) (map termJoin args)
termJoin (App Bottom args) = App Bottom (map termJoin args)
termJoin (App ConsZero args) = App ConsZero (map termJoin args)
termJoin (App ConsSucc args) = App ConsSucc (map termJoin args)
termJoin (App NatCase args) = App NatCase (map termJoin args)
termJoin (Lam s t) = Lam s (termJoin t)

termCast :: Term Void -> Term m
termCast = fmap absurd

app :: Term m -> Term m -> Term m
app (App hd args) u = App hd (args ++ [u])
app (Lam s t) u = subst s u t

appN :: Term m -> [Term m] -> Term m
appN = foldl app

subst :: String -> Term m -> Term m -> Term m
subst s t (Lam s' t')
  | s /= s' = Lam s' (subst s t t')
subst s t (App hd args) = appN (substVar s t hd) (map (subst s t) args)
subst _ _ m = m

substVar :: String -> Term m -> Var m -> Term m
substVar s t (Bound s')
  | s == s' = t
substVar _ _ t = App t []

-- Fresh names:

{-# NOINLINE giveMeFresh #-}
giveMeFresh :: a -> Integer
giveMeFresh _ = unsafePerformIO fresh

{-# NOINLINE fresh #-}
fresh :: IO Integer
fresh = do
  atomicModifyIORef ctr (\i -> (i + 1, i))
  where
    ctr :: IORef Integer
    ctr = unsafePerformIO $ newIORef 0
