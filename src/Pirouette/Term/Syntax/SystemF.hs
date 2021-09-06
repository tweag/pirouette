{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveFoldable       #-}
module Pirouette.Term.Syntax.SystemF where

import           Pirouette.Term.Syntax.Subst

import qualified PlutusCore        as P
import qualified PlutusCore.Pretty as P

import           Control.Arrow (first)
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Data.Maybe (mapMaybe)
import           Data.Either (fromRight)
import           Data.Foldable
import qualified Data.Set   as S
import           Data.List  (foldl')
import           Data.Typeable
import qualified Data.Text as T
import           Data.String
import           Data.Data
import           Data.Generics.Uniplate.Operations
import           Data.Generics.Uniplate.Data

-- * System F

-- ** Annotated Variables

data Var ann f = B (Ann ann) Integer | F f
  deriving (Eq, Ord, Functor, Show, Data, Typeable, Foldable, Traversable)

instance IsVar (Var ann f) where
  type VarAnn (Var ann f) = ann

  isBound (B _ i) = Just i
  isBound _       = Nothing

  varMapM f (B ann i) = B ann <$> f i
  varMapM _ v         = return v

  annMap f (B (Ann a) i) = B (Ann (f a)) i
  annMap _ v       = v

-- ** Kinds

data Kind = KStar | KTo Kind Kind
  deriving (Eq, Ord, Show, Data, Typeable)

-- ** Types

data AnnType ann ty
  = TyApp ty [AnnType ann ty]
  | TyFun (AnnType ann ty) (AnnType ann ty)
  | TyLam (Ann ann) Kind (AnnType ann ty)
  | TyAll (Ann ann) Kind (AnnType ann ty)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

tyFlatten :: (IsVar v) => AnnType ann (AnnType ann v) -> AnnType ann v
tyFlatten (TyApp x args) = appN x $ map tyFlatten args
tyFlatten (TyFun t u)    = TyFun (tyFlatten t) (tyFlatten u)
tyFlatten (TyLam v k t)  = TyLam v k $ tyFlatten t
tyFlatten (TyAll v k t)  = TyAll v k $ tyFlatten t

tyBimapM :: (Monad m) => (ann -> m ann') -> (ty -> m ty')
         -> AnnType ann ty -> m (AnnType ann' ty')
tyBimapM f g (TyApp n args) = TyApp <$> g n <*> mapM (tyBimapM f g) args
tyBimapM f g (TyFun t u)    = TyFun <$> tyBimapM f g t <*> tyBimapM f g u
tyBimapM f g (TyLam a k u)  = TyLam <$> mapM f a <*> return k <*> tyBimapM f g u
tyBimapM f g (TyAll a k u)  = TyAll <$> mapM f a <*> return k <*> tyBimapM f g u

type Type v = AnnType (VarAnn v) v

tyFunArgs :: AnnType ann ty -> ([AnnType ann ty], AnnType ann ty)
tyFunArgs (TyFun u t) = first (u :) $ tyFunArgs t
tyFunArgs t           = ([], t)

-- |Given a @t : AnnType ann ty@, returns how many arguments would we
-- have to provide a @AnnTerm@ of type @t@ to fully saturate it. This includes
-- type arguments!
tyArity :: AnnType ann ty -> Int
tyArity (TyAll _ _ t) = 1 + tyArity t
tyArity t             = tyMonoArity t

-- |Unlike 'tyArity', we only compute how many term arguments a term of
-- the given type has to receive
tyMonoArity :: AnnType ann ty -> Int
tyMonoArity = length . fst . tyFunArgs

tyPure :: ty -> AnnType ann ty
tyPure = flip TyApp []

instance (IsVar v) => HasSubst (AnnType ann v) where
  type SubstVar (AnnType ann v) = v
  var = tyPure

  subst s (TyApp n xs)  = appN (applySub s n) $ map (subst s) xs
  subst s (TyFun t u)   = TyFun (subst s t) (subst s u)
  subst s (TyLam v k t) = TyLam v k (subst (liftSub s) t)
  subst s (TyAll v k t) = TyAll v k (subst (liftSub s) t)

tyApp :: (IsVar v) => AnnType ann v -> AnnType ann v -> AnnType ann v
tyApp (TyApp n args) u = TyApp n (args ++ [u])
tyApp (TyLam _ _ t)  u = subst (singleSub u) t
tyApp (TyAll _ _ t)  u = subst (singleSub u) t
tyApp (TyFun _ _)    _ = error "Can't apply TyFun"

-- TODO: write an efficient appN that substitutes multiple variables in one go
instance HasApp (AnnType ann) where
  type AppArg (AnnType ann) v = AnnType ann v
  appN = foldl' tyApp

-- ** Terms

data AnnTerm ty ann v
  = App   v              [Arg ty (AnnTerm ty ann v)]
  | Lam   (Ann ann) ty   (AnnTerm ty ann v)
  | Abs   (Ann ann) Kind (AnnTerm ty ann v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

termTyFoldMap :: (Monoid m) => (ty -> m) -> AnnTerm ty ann v -> m
termTyFoldMap f (App _ args) = mconcat $ mapMaybe (fmap f . fromTyArg) args
termTyFoldMap f (Lam _ ty u) = f ty <> termTyFoldMap f u
termTyFoldMap f (Abs _ _  u) = termTyFoldMap f u

termAnnFold :: (Monoid m) => (ann -> m) -> AnnTerm ty ann v -> m
termAnnFold f (App _ args) = mconcat $ mapMaybe (fmap (termAnnFold f) . fromArg) args
termAnnFold f (Lam (Ann x) _ u) = f x <> termAnnFold f u
termAnnFold f (Abs (Ann x) _ _) = f x

termTriMap :: (ty -> ty') -> (ann -> ann') -> (v -> v')
            -> AnnTerm ty ann v -> AnnTerm ty' ann' v'
termTriMap f g h (App n args) = App (h n) $ map (argMap f (termTriMap f g h)) args
termTriMap f g h (Lam a ty u) = Lam (fmap g a) (f ty) (termTriMap f g h u)
termTriMap f g h (Abs a k  u) = Abs (fmap g a) k (termTriMap f g h u)

termTrimapM :: (Monad m) => (ty -> m ty') -> (ann -> m ann') -> (v -> m v')
            -> AnnTerm ty ann v -> m (AnnTerm ty' ann' v')
termTrimapM f g h (App n args) = App <$> h n <*> mapM (argMapM f (termTrimapM f g h)) args
termTrimapM f g h (Lam a ty u) = Lam <$> mapM g a <*> f ty <*> termTrimapM f g h u
termTrimapM f g h (Abs a k  u) = Abs <$> mapM g a <*> return k <*> termTrimapM f g h u

termTyMapM :: (Monad m) => (ty -> m ty') -> AnnTerm ty ann v -> m (AnnTerm ty' ann v)
termTyMapM f = termTrimapM f return return

termTyMap :: (ty -> ty') -> AnnTerm ty ann v -> AnnTerm ty' ann v
termTyMap f = runIdentity . termTyMapM (return . f)

-- |Applies a transformation to the fist application we find while
-- descending down a chain of lambda abstractions. The abstractions
-- are preserved.
preserveLamsM :: (Monad m)
              => (Integer -> AnnTerm ty ann f -> m (AnnTerm ty ann f))
              -> AnnTerm ty ann f -> m (AnnTerm ty ann f)
preserveLamsM f (Lam ann ty t) = Lam ann ty <$> preserveLamsM (\n -> f (n+1)) t
preserveLamsM f t                = f 0 t

preserveLams :: (Integer -> AnnTerm ty ann f -> AnnTerm ty ann f)
              -> AnnTerm ty ann f -> AnnTerm ty ann f
preserveLams f = runIdentity . preserveLamsM (\i -> return . f i)

getHeadAbs :: AnnTerm ty ann f -> ([(ann, Kind)], AnnTerm ty ann f)
getHeadAbs (Abs (Ann v) k t) = first ((v, k):) $ getHeadAbs t
getHeadAbs t                 = ([], t)

getHeadLams :: AnnTerm ty ann f -> ([(ann, ty)], AnnTerm ty ann f)
getHeadLams (Lam (Ann v) ty t) = first ((v, ty):) $ getHeadLams t
getHeadLams t                  = ([], t)

getNHeadLams :: Int -> AnnTerm ty ann f -> ([(ann, ty)], AnnTerm ty ann f)
getNHeadLams 0 t                  = ([], t)
getNHeadLams n (Lam (Ann v) ty t) = first ((v, ty):) $ getNHeadLams (n-1) t
getNHeadLams _ _                  = error "getNHeadLams: Not enough lambdas"

getHeadTyAbs :: AnnTerm ty ann f -> ([(ann, Kind)], AnnTerm ty ann f)
getHeadTyAbs (Abs (Ann v) k t) = first ((v, k):) $ getHeadTyAbs t
getHeadTyAbs t                  = ([], t)

withLams :: [(ann, ty)] -> AnnTerm ty ann f -> AnnTerm ty ann f
withLams = foldr (\bv t -> uncurry Lam (first Ann bv) . t) id

data Arg ty v
  = TyArg ty
  | Arg v
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

argElim :: (ty -> a) -> (v -> a) -> Arg ty v -> a
argElim f g (Arg x)   = g x
argElim f g (TyArg x) = f x

fromArg :: Arg ty v -> Maybe v
fromArg = argElim (const Nothing) Just

fromTyArg :: Arg ty v -> Maybe ty
fromTyArg = argElim Just (const Nothing)

isArg :: Arg ty v -> Bool
isArg = argElim (const False) (const True)

isTyArg :: Arg ty v -> Bool
isTyArg = argElim (const True) (const False)

pattern Free :: v -> AnnTerm ty ann' (Var ann v)
pattern Free f = App (F f) []

type Term ty v = AnnTerm ty (VarAnn v) v

argMapM :: (Monad m) => (ty -> m ty') -> (v -> m v') -> Arg ty v -> m (Arg ty' v')
argMapM f g (TyArg x) = TyArg <$> f x
argMapM f g (Arg x)   = Arg <$> g x

argMap :: (ty -> ty') -> (v -> v') -> Arg ty v -> Arg ty' v'
argMap f g = runIdentity . argMapM (return . f) (return . g)

termFlatten :: (HasSubst ty, IsVar v) => AnnTerm ty ann (AnnTerm ty ann v) -> AnnTerm ty ann v
termFlatten (App x args) = appN x $ map (argMap id termFlatten) args
termFlatten (Lam v k t)  = Lam v k $ termFlatten t
termFlatten (Abs v k t)  = Abs v k $ termFlatten t

termPure :: v -> AnnTerm ty ann v
termPure = flip App []

instance (HasSubst ty, IsVar v) => HasSubst (AnnTerm ty ann v) where
  type SubstVar (AnnTerm ty ann v) = v
  var = termPure

  subst s (App n xs)  = appN (applySub s n) $ map (argMap id (subst s)) xs
  subst s (Lam v k t) = Lam v k (subst (liftSub s) t)
  subst s (Abs v k t) = Abs v k (subst s t)

substTy :: (HasSubst ty)
        => Sub ty -> AnnTerm ty ann v -> AnnTerm ty ann v
substTy s (App n args)    = App n (map (argMap (subst s) (substTy s)) args)
substTy s (Lam v ty body) = Lam v (subst s ty) (substTy s body)
substTy s (Abs v kd body) = Abs v kd (substTy (liftSub s) body)

termApp :: (HasSubst ty, IsVar v)
        => AnnTerm ty ann v -> Arg ty (AnnTerm ty ann v)
        -> AnnTerm ty ann v
termApp (App n args)        u  = App n (args ++ [u])
termApp (Lam _ _ t)  (Arg   u) = subst   (singleSub u) t
termApp (Abs _ _ t)  (TyArg u) = substTy (singleSub u) t
termApp _            _         = error "Mismatched Term/Type application"

-- |Expands a single definition within another term.
--
-- WARNING: When calling @expandvar (n, defn) m@, ensure that @defn@ does /not/
-- depend on @n@, i.e., @n@ can't be recursive. 'expandVar' will /not/
-- perform this check and will happily loop.
--
-- WARNING: Although we're using De Bruijn indices, some code generation targets
-- such as TLA+ are very unhappy about name shadowing, so you might want to map
-- over the result and deshadow bound names.
expandVar :: (HasSubst ty, Eq v, IsVar v, Data ty, Data ann, Data v)
          => (v, AnnTerm ty ann v) -> AnnTerm ty ann v -> AnnTerm ty ann v
expandVar (n, defn) = rewrite go
  where
    go (App v args)
      | n /= v    = Nothing
      | otherwise = Just $ appN defn args
    go _ = Nothing

-- TODO: write an efficient appN that substitutes multiple variables in one go
instance (HasSubst ty) => HasApp (AnnTerm ty ann) where
  type AppArg (AnnTerm ty ann) v = Arg ty (AnnTerm ty ann v)
  appN = foldl' termApp

-- |Maps a function over names, keeping track of how the scope by counting
-- how many lambdas have we traversed
mapNameScoped :: (Integer -> v -> v) -> AnnTerm ty ann v -> AnnTerm ty ann v
mapNameScoped f = go 0
  where
    go c (Abs t k body) = Abs t k (go c body)
    go c (Lam v t body) = Lam v t $ go (c+1) body
    go c (App n args)   = App (f c n) $ map (argMap id (go c)) args

-- |Permute the free variables of a term according to a function f
permute :: (IsVar v) => (Integer -> Integer) -> AnnTerm ty ann v -> AnnTerm ty ann v
permute f = mapNameScoped (varMap . permName)
  where
    permName c i = if i >= c then c + f (i - c) else i

-- * Auxiliary Defs

-- ** N-ary Reducing Applications

class HasApp term where
  type AppArg term v :: *
  appN :: (IsVar v) => term v -> [AppArg term v] -> term v

app :: (IsVar v, HasApp term) => term v -> AppArg term v -> term v
app t = appN t . (:[])

-- * Renaming of bound variables

renameFirstBounds :: (IsVar v)
                  => [VarAnn v] -> AnnTerm ty (VarAnn v) v
                  -> AnnTerm ty (VarAnn v) v
renameFirstBounds l =
  let f c x = case isBound x of
        Just i  ->
          if i < c
          then x
          else
            let i_int = fromInteger (i - c) in
            if i_int < length l then annMap (const (l !! i_int)) x else x
        Nothing -> x
  in
  mapNameScoped f

-- ** Proof-Irrelevant Annotations

newtype Ann x = Ann { ann :: x }
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)

instance Eq (Ann x) where
  _ == _ = True

instance Ord (Ann x) where
  compare _ _ = EQ

instance IsString x => IsString (Ann x) where
  fromString = Ann . fromString
