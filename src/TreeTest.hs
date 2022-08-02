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

data TermSet
  = Simple {unTermSet :: Tree (Spines TermSet)}
  | Inst {unMeta :: Meta, unTermSet :: Tree (Spines TermSet)}

instance Show TermSet where
  show (Simple _) = "<simple-ts>"
  show (Inst m _) = "ts$" ++ show m

data CotrInfo = CIZero | CISucc

-- Spine Layer
data S r
  = Call ([TermSet] -> r) TermSet
  | Dest ((CotrInfo, [TermSet]) -> r) TermSet
  | Cotr CotrInfo [r]
  | Bot

instance Functor S where
  fmap f Bot = Bot
  fmap f (Cotr ci rs) = Cotr ci $ fmap f rs
  fmap f (Dest cs mot) = Dest (f . cs) mot
  fmap f (Call func args) = Call (f . func) args

data Spines r
  = One (S (Spines r))
  | None r
  deriving (Functor)

instance Show (Spines r) where
  show _ = "<spine>"

spinesJoin :: Spines (Spines r) -> Spines r
spinesJoin (None r) = r
spinesJoin (One s) = One $ fmap spinesJoin s

data Tree a
  = Leaf a
  | Learn String (Tree a)
  | Branch [Tree a]
  deriving (Show, Functor)

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
       in Simple $
            Learn (show vs) $
              Leaf $ evalChooseLoop (S.fromList vs, appN (termCast t) (map meta vs))

    evalChooseLoop :: ScopedTerm -> Spines TermSet
    evalChooseLoop t = trace inf $ fmap termSet . eval $ t
      where
        inf = "evalChooseLoop: " ++ show t

    termSet :: ScopedMeta -> TermSet
    termSet = uncurry Inst . choose

    eval :: ScopedTerm -> Spines ScopedMeta
    eval (s, t) = (\m -> (S.insert m s, m)) <$> eval1 _ t

    eval1 :: (m -> TermSet) -> Term m -> Spines m
    eval1 f Lam {} = error "Lam has no eval"
    eval1 f t@(App hd args) =
      case hd of
        ConsSucc -> One $ Cotr CISucc [eval1 f $ head args]
        ConsZero -> One $ Cotr CIZero []
        NatCase -> case args of
          [mot, cZ, cS] -> One $
            flip Dest (_eval1 mot) $ \case
              (CIZero, []) -> eval1 f cZ
              (CISucc, [x]) -> magic2 cS [x]
              _ -> error "type error"
          _ -> error "too little args to NatCase"
        Bound _ -> error "Bound head"
        Meta n -> None n
        Bottom -> One Bot
        Free n ->
          let bodyN = termCast $ defs M.! n
           in magic bodyN $ map (eval1 f) args

    choose :: ScopedMeta -> (Meta, Tree (Spines TermSet))
    choose (s, n) = (n,) $
      Branch $
        flip map [CIZero, CISucc] $ \cons ->
          let (vs, cotr) = mkSymbolicCotr cons
              res = "$s" ++ show (unsafePerformIO fresh)
           in Learn ("(++ " ++ show vs ++ ")") $
                Learn (res ++ " == " ++ show vs) $ Leaf $ evalChooseLoop (S.union s vs, cotr)

    magic :: forall m. (Show m) => Term m -> [Spines m] -> Spines m
    magic body args =
      let body' = fmap None body
          args' = map meta args
          res :: Term (Spines m)
          res = body' `appN` args'
       in spinesJoin $ eval1 _ res

magic2 :: Term m -> [TermSet] -> Spines m
magic2 = _

mkSymbolicCotr :: CotrInfo -> (S.Set Meta, Term Meta)
mkSymbolicCotr CIZero = (S.empty, App ConsZero [])
mkSymbolicCotr CISucc =
  let v = "$s" ++ show (unsafePerformIO fresh)
   in (S.singleton v, App ConsSucc [meta v])

------

data CallConvention
  = CallByName
  | CallByValue

type State = [String]

cata :: CallConvention -> Integer -> TermSet -> [(State, Term Meta)]
cata cc depth = go depth []
  where
    go :: Integer -> State -> TermSet -> [(State, Term Meta)]
    go n st (Inst m ts)
      | n <= 0 = return (st, meta m)
      | otherwise = goAux n st ts
    go n st (Simple ts) = goAux n st ts

    goAux :: Integer -> State -> Tree (Spines TermSet) -> [(State, Term Meta)]
    goAux n st = concatMap (uncurry goAgain) . goWHNF n st
      where
        goAgain :: State -> Term TermSet -> [(State, Term Meta)]
        goAgain st' t = do
          t' <- termDistr $ fmap (go (n - 1) st') t
          let (sts, t'') = termStr t'
          let sts' = if null sts then st' else mconcat sts
          return (sts', termJoin t'')

    goWHNF :: (Show a) => Integer -> State -> Tree (Spines a) -> [(State, Term a)]
    goWHNF n st ts = concatMap (uncurry (goSpines n)) $ goTree st ts

    goTree :: State -> Tree a -> [(State, a)]
    goTree st (Learn s t) = goTree (s : st) t
    goTree st (Branch ts) = asum $ map (goTree st) ts
    goTree st (Leaf x) = return (st, x)

    goSpines :: (Show a) => Integer -> State -> Spines a -> [(State, Term a)]
    goSpines n st (None a) = return (st, meta a)
    goSpines n st (One s) =
      case s of
        Bot -> return (st, bottom)
        Cotr ci rs ->
          case ci of
            CIZero -> return (st, App ConsZero [])
            CISucc -> do
              -- because this is succ, we know it has one argument
              (st', rs') <- combineArgs st <$> traverse (goSpines (n - 1) st) rs
              return (st', App ConsSucc rs')
        Call f args -> case cc of
          CallByName -> goSpines n st (f args)
          CallByValue -> undefined
        Dest f x -> do
          (st', x') <- goSpines n st x
          case x' of
            (App ConsZero as) -> goSpines n st' $ f (CIZero, as)
            (App ConsSucc as) -> goSpines n st' $ f (CISucc, as)
            (App hd _) -> error $ "Type Error: App " ++ show hd
            (Lam s _) -> error $ "Type Error: Lam " ++ show s

    combineArgs :: State -> [(State, a)] -> (State, [a])
    combineArgs s0 [] = (s0, [])
    combineArgs s0 xs = first concat . unzip $ xs

cataIO :: CallConvention -> Integer -> TermSet -> IO ()
cataIO cc n t = mapM_ (uncurry pretty) $ cata cc n t
  where
    pretty strs res =
      putStrLn $ "- " ++ show res -- ++ "\n" ++ unlines (map ("    " ++) strs)

-----------------

add :: (String, Term m)
add =
  ( "add",
    Lam "n" $
      Lam "m" $
        App
          NatCase
          [ bound "n",
            bound "m",
            Lam "sn" $ App ConsSucc [appN (free "add") [bound "sn", bound "m"]]
          ]
  )

constF :: (String, Term m)
constF = ("const", Lam "n" $ Lam "m" $ bound "n")

defs :: Defs
defs = M.fromList [add, constF]

res :: CallConvention -> Integer -> IO ()
res cc n =
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

--

instance Applicative Tree where
  pure = Leaf
  (<*>) = ap

instance Monad Tree where
  Leaf x >>= f = f x
  Learn str t >>= f = Learn str (t >>= f)
  Branch ts >>= f = Branch $ map (>>= f) ts

distr :: [Tree a] -> Tree [a]
distr [] = Leaf []
distr (tx : txs) = (:) <$> tx <*> distr txs

-- Fresh names:

{-# NOINLINE fresh #-}
fresh :: IO Integer
fresh = do
  atomicModifyIORef ctr (\i -> (i + 1, i))
  where
    ctr :: IORef Integer
    ctr = unsafePerformIO $ newIORef 0
