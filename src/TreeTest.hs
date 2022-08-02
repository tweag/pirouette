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
import System.IO.Unsafe

----------------------------------------
-- Term type to symbolically execute: --
----------------------------------------

data Term m
  = Lam String (Term m)
  | App (Var m) [Term m]
  | NatCase (Term m) (Term m) (Term m)
  | ConsZero
  | ConsSucc (Term m)
  deriving (Show, Functor)

data Var m
  = Bound String
  | Free String
  | Meta m
  | Bottom
  deriving (Show, Functor)

type Defs = M.Map String (Term Void)

type Meta = String

------------------------------------------------
-- Infinite trees, giving semantics to terms: --
------------------------------------------------

data TermSet
  = Simple {unTermSet :: Tree (Spines TermSet)}
  | Inst {unMeta :: Meta, unTermSet :: Tree (Spines TermSet)}

data CotrInfo = CIZero | CISucc

-- Spine Layer
data S r
  = forall a. Call ([Spines a] -> r) [Spines a]
  | forall a. Dest ((CotrInfo, [Term a]) -> r) (Spines a)
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

-- The anamorphism!
symbolically :: Defs -> Term Void -> TermSet
symbolically defs = withSymVars []
  where
    withSymVars :: [Meta] -> Term Void -> TermSet
    withSymVars s (Lam n t) = withSymVars (n : s) t
    withSymVars s body =
      Simple $
        Learn (show s) $
          Leaf $ evalChooseLoop (S.fromList s, appN (termCast body) (map meta s))

    evalChooseLoop :: ScopedTerm -> Spines TermSet
    evalChooseLoop = fmap termSet . eval

    termSet :: ScopedMeta -> TermSet
    termSet = uncurry Inst . choose

    eval :: ScopedTerm -> Spines ScopedMeta
    eval (s, t) = (\m -> (S.insert m s, m)) <$> eval1 t

    eval1 :: Term m -> Spines m
    eval1 Lam {} = error "Lam has no eval"
    eval1 ConsZero = One $ Cotr CIZero []
    eval1 (ConsSucc t) = One $ Cotr CISucc [eval1 t]
    eval1 (NatCase mot cZ cS) = One $
      flip Dest (eval1 mot) $ \case
        (CIZero, []) -> eval1 cZ
        (CISucc, [x]) -> eval1 $ cS `appN` [x]
        _ -> error "type error"
    eval1 t@(App hd args) =
      case hd of
        Bound _ -> error "Bound head"
        Meta n -> None n
        Bottom -> One Bot
        Free n ->
          let bodyN = termCast $ defs M.! n
           in magic bodyN $ map eval1 args

    choose :: ScopedMeta -> (Meta, Tree (Spines TermSet))
    choose (s, n) = (n,) $
      Branch $
        flip map [CIZero, CISucc] $ \cons ->
          let (vs, cotr) = mkSymbolicCotr cons
              res = "$s" ++ show (unsafePerformIO fresh)
           in Learn ("(++ " ++ show vs ++ ")") $
                Learn (res ++ " == " ++ show vs) $ Leaf $ evalChooseLoop (S.union s vs, cotr)

    magic :: forall m. Term m -> [Spines m] -> Spines m
    magic body args =
      let body' = fmap None body
          args' = map meta args
          res :: Term (Spines m)
          res = body' `appN` args'
       in spinesJoin $ eval1 res

mkSymbolicCotr :: CotrInfo -> (S.Set Meta, Term Meta)
mkSymbolicCotr CIZero = (S.empty, ConsZero)
mkSymbolicCotr CISucc =
  let v = "$s" ++ show (unsafePerformIO fresh)
   in (S.singleton v, ConsSucc (meta v))

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

    goWHNF :: Integer -> State -> Tree (Spines a) -> [(State, Term a)]
    goWHNF n st ts = concatMap (uncurry (goSpines n)) $ goTree st ts

    goTree :: State -> Tree a -> [(State, a)]
    goTree st (Learn s t) = goTree (s : st) t
    goTree st (Branch ts) = asum $ map (goTree st) ts
    goTree st (Leaf x) = return (st, x)

    goSpines :: Integer -> State -> Spines a -> [(State, Term a)]
    goSpines n st (None a) = return (st, meta a)
    goSpines n st (One s) =
      case s of
        Bot -> return (st, bottom)
        Cotr ci rs ->
          case ci of
            CIZero -> return (st, ConsZero)
            CISucc -> do
              -- because this is succ, we know it has one argument
              (st', [rs']) <- combineArgs st <$> traverse (goSpines (n - 1) st) rs
              return (st', ConsSucc rs')
        Call f args -> case cc of
          CallByName -> goSpines n st (f args)
          CallByValue -> undefined
        Dest f x -> do
          (st', x') <- goSpines n st x
          case x' of
            ConsZero -> goSpines n st' $ f (CIZero, [])
            ConsSucc as -> goSpines n st' $ f (CISucc, [as])
            _ -> error "Type Error"

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
        NatCase
          (bound "n")
          (bound "m")
          (Lam "sn" $ ConsSucc $ appN (free "add") [bound "sn", bound "m"])
  )

constF :: (String, Term m)
constF = ("const", Lam "n" $ Lam "m" $ bound "n")

defs :: Defs
defs = M.fromList [add, constF]

res :: CallConvention -> Integer -> IO ()
res cc n =
  cataIO cc n $
    symbolically defs $ Lam "k" (appN (free "add") [bound "k", ConsSucc (bound "k")])

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
termDistr (NatCase m z s) = NatCase <$> termDistr m <*> termDistr z <*> termDistr s
termDistr ConsZero = pure ConsZero
termDistr (ConsSucc n) = ConsSucc <$> termDistr n

varDistr :: (Applicative f) => Var (f a) -> f (Var a)
varDistr (Bound s) = pure (Bound s)
varDistr (Free s) = pure (Free s)
varDistr Bottom = pure Bottom
varDistr (Meta s) = Meta <$> s

termStr :: Term (a, b) -> ([a], Term b)
termStr (App fa args) =
  let (a1, fa') = varStr fa
      (as, args') = unzip $ map termStr args
   in (a1 ++ concat as, App fa' args')
termStr (Lam s t) = second (Lam s) (termStr t)
termStr (NatCase m z s) =
  let (a1, m') = termStr m
      (a2, z') = termStr z
      (a3, s') = termStr s
   in (a1 ++ a2 ++ a3, NatCase m' z' s')
termStr ConsZero = pure ConsZero
termStr (ConsSucc n) = second ConsSucc $ termStr n

varStr :: Var (a, b) -> ([a], Var b)
varStr (Bound s) = ([], Bound s)
varStr (Free s) = ([], Free s)
varStr Bottom = ([], Bottom)
varStr (Meta (a, b)) = ([a], Meta b)

termJoin :: Term (Term a) -> Term a
termJoin (App (Meta m) args) = appN m (map termJoin args)
termJoin (App (Bound s) args) = App (Bound s) (map termJoin args)
termJoin (App (Free s) args) = App (Free s) (map termJoin args)
termJoin (App Bottom args) = App Bottom (map termJoin args)
termJoin (Lam s t) = Lam s (termJoin t)
termJoin (NatCase m z s) = NatCase (termJoin m) (termJoin z) (termJoin s)
termJoin (ConsSucc s) = ConsSucc (termJoin s)
termJoin ConsZero = ConsZero

termCast :: Term Void -> Term m
termCast = fmap absurd

app :: Term m -> Term m -> Term m
app (App hd args) u = App hd (args ++ [u])
app (Lam s t) u = subst s u t
app t u =
  error $
    unlines
      [ "Cant app: ",
        "t " ++ show (fmap (const ()) t),
        "u " ++ show (fmap (const ()) u)
      ]

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
