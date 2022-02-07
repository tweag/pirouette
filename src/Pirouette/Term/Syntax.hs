{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Pirouette.Term.Syntax
  ( module EXPORT
  , PrtTerm, PrtType, PrtDef, PrtTypeDef, PrtArg
  , PrtTermMeta, PrtTypeMeta, PrtArgMeta
  , PrtVar, PrtTyVar
  , PrtVarMeta, PrtTyVarMeta
  , Name(..), ToName(..), TyName
  , prtTypeToMeta , prtTypeFromMeta
  , prtTermToMeta
  , separateBoundFrom
  , declsUniqueNames
  , safeIdx
  , unsafeIdx
  ) where

import           Pirouette.Term.Syntax.Base    as EXPORT
import           Pirouette.Term.Syntax.Pretty  as EXPORT
import qualified Pirouette.Term.Syntax.SystemF as R
import  Pirouette.Term.Syntax.Subst

import           Control.Monad.State
import           Control.Monad.Reader
import Data.Bifunctor (first)
import qualified Data.List                 as L
import qualified Data.Text                 as T
import qualified Data.Map.Strict           as M
import qualified Data.Set                  as S
import           Data.Data
import           Data.String
import           Data.Maybe (fromMaybe)
import Pirouette.Term.Syntax.Pretty.Class
import Data.Void
import Control.Monad.Identity

-- * Top Level Terms and Types
--
-- $toplvlterms
--
-- Pirouette terms and types are simply 'Term' and 'Type' with their type variables
-- instantiated.

type PrtTerm lang = Term lang Name
type PrtTermMeta lang m = TermMeta lang m Name
type PrtType lang = Type lang Name
type PrtTypeMeta lang m = TypeMeta lang m Name
type PrtArgMeta lang m = R.Arg (PrtTypeMeta lang m) (PrtTermMeta lang m)
type PrtArg  lang = R.Arg (PrtType lang) (PrtTerm lang)

type PrtDef lang = Definition lang Name
type PrtTypeDef lang = TypeDef lang Name

type PrtVar lang = R.Var Name (TermBase lang Name)
type PrtVarMeta lang meta = R.VarMeta meta Name (TermBase lang Name)
type PrtTyVar lang = R.Var Name (TypeBase lang Name)
type PrtTyVarMeta lang meta = R.VarMeta meta Name (TypeBase lang Name)

prtTypeMetaMapM :: (Monad m) => (meta -> m meta')
                -> PrtTypeMeta lang meta
                -> m (PrtTypeMeta lang meta')
prtTypeMetaMapM f = R.tyBimapM return (R.varMapMetaM f)

prtTypeToMeta :: PrtType lang -> PrtTypeMeta lang meta
prtTypeToMeta = runIdentity . prtTypeMetaMapM absurd

prtTypeFromMeta :: PrtTypeMeta lang meta -> PrtType lang
prtTypeFromMeta = runIdentity . prtTypeMetaMapM (const $ error "Type with metavariables")

prtTermMetaMapM :: (Monad m) => (meta -> m meta')
                -> PrtTermMeta lang meta
                -> m (PrtTermMeta lang meta')
prtTermMetaMapM f = R.termTrimapM (prtTypeMetaMapM f) return (R.varMapMetaM f)

prtTermToMeta :: PrtTerm lang -> PrtTermMeta lang meta
prtTermToMeta = runIdentity . prtTermMetaMapM absurd

-- * Names

-- |Our own name type. This is useful because since we're producing code that
-- is supposed to be humanly readable, we might want to remove the 'nameUnique'
-- part of non-ambiguous names.
data Name = Name { nameString :: T.Text, nameUnique :: Maybe Int }
  deriving (Eq , Ord, Data, Typeable)

-- |We'll just define a 'TyName' synonym to keep our Haskell type-signatures
-- more organized.
type TyName = Name

instance Show Name where
  show (Name str i) = T.unpack str <> maybe mempty show i

instance IsString Name where
  fromString = flip Name Nothing . T.pack

instance Pretty Name where
  pretty (Name str i) = pretty str <> maybe mempty pretty i

class ToName v where
  toName :: v -> Name

-- | @separateBoundFrom u t@ outputs @t@ where all the bound variables occuring in both terms
-- are renamed to avoid name clashes when outputting code that relies on user given names
-- while still being able to use something close to the programmer-given names for the
-- generated code.
separateBoundFrom :: Term lang Name -> Term lang Name -> Term lang Name
separateBoundFrom u t =
  let boundOf = R.termAnnFold S.singleton in
  let inter = S.intersection (boundOf u) (boundOf t) in
  if null inter
  then t
  else
    -- `structuredInter` transforms the set of name clashes into a map
    -- from nameString to the list of nameUnique associated.
    let structuredInter =
          S.fold
            (\n m -> M.insertWith (++) (nameString n) [nameUnique n] m)
            M.empty
            inter
    in
    -- `nextFresh s txt i n` takes a set `s` of names and a `nameString` `txt` and outputs
    -- the first index which does not create clash.
    -- `n` starts from 0 and increases until a number not already taken is met,
    -- whereas `i` counts how much new number must be met.
    -- The purpose of `i` is to avoid to rename identically `x0` and `x1`
    -- if both are subject to name clash.
    let nextFresh :: S.Set Name -> T.Text -> Int -> Int -> Name
        nextFresh s txt i n
          | S.member (Name txt (Just n)) s = nextFresh s txt i (n + 1)
          | i == 0 = Name txt (Just n)
          | otherwise = nextFresh s txt (i - 1) (n + 1)
    in
    let rename :: M.Map T.Text [Maybe Int] -> S.Set Name -> Name -> Name
        rename m s n@(Name txt u) =
          case M.lookup txt m of
            Nothing -> n
            Just x ->
              case L.elemIndex u x of
                Nothing -> n
                Just i -> nextFresh s txt i 0
    in
    let f = rename structuredInter (S.union (boundOf u) (boundOf t)) in
    R.termTriMap id f (annMap f) t


-- ** Uniquely Naming
--
-- $uniquenames
--
-- Defines a number of functions for removing all the unnecessary 'nameUnique' parts.
-- This not only enables us to ignore De Bruijn indicies in future steps, but produces
-- far more readable TLA+ code.
--
-- Worth noting that even though PlutusIR is guaranteed to have unique names as of now,
-- because we're normalizing terms, its better to do so with De Bruijn indices. Moreover,
-- it makes sure we don't need to worry about alpha equivalence of terms.
-- Finally, it happened before that we couldn't trust the pretty printer:
-- https://github.com/input-output-hk/plutus/issues/3445

-- |Exported interface function to uniquely naming declarations.
declsUniqueNames :: Decls lang Name -> PrtTerm lang -> (Decls lang Name, PrtTerm lang)
declsUniqueNames decls mainFun = first M.fromList (go (M.toList decls) mainFun)
  where
    onPairM f g (x, y) = (,) <$> f x <*> g y

    go :: [(Name, Definition lang Name)] -> PrtTerm lang
       -> ([(Name , Definition lang Name)], PrtTerm lang)
    go ds mainFun =
      let (_, ks) =
            flip runState M.empty $ mapM (onPairM unNameCollect defUNCollect) ds
      in
      runReader
        (onPairM (mapM (onPairM unNameSubst defUNSubst)) termUNSubst (ds, mainFun))
        (M.map S.toList ks)

-- *** Auxiliar Definitions for Unique Naming
--
-- $uniquenamesaux
--
-- The unique naming algorithm is simple: we collect all names used in a map
-- from their nameString to the set of names that are used and share the same
-- nameString. We then convert those sets to lists and substitute names accordingly.
-- If a name shares no nameString with no other name, we ignore nameUnique.

type UNCollectM = State (M.Map T.Text (S.Set Name))
type UNSubstM   = Reader (M.Map T.Text [Name])

-- We use 'flip S.union' because S.union is more efficient on S.union bigset smallset
-- and 'M.insertWith f k x' applies 'f x old_value' when there is a collision; hence,
-- old_value will be the larger set.
unNameCollect :: Name -> UNCollectM Name
unNameCollect n = modify (M.insertWith (flip S.union) (nameString n) (S.singleton n)) >> return n

defUNCollect :: Definition lang Name -> UNCollectM (Definition lang Name)
defUNCollect (DFunction r t ty) = DFunction r <$> termUNCollect t <*> typeUNCollect ty
defUNCollect (DConstructor i n) = DConstructor i <$> unNameCollect n
defUNCollect (DDestructor n)    = DDestructor <$> unNameCollect n
defUNCollect (DTypeDef n)       = DTypeDef <$> unTypeDefCollect n

unTypeDefCollect :: TypeDef lang Name -> UNCollectM (TypeDef lang Name)
unTypeDefCollect d@(Datatype _ _ dest cons) = do
  void $ unNameCollect dest
  let (consNames, types) = unzip cons
  mapM_ unNameCollect consNames
  mapM_ typeUNCollect types
  return d

termUNCollect :: Term lang Name -> UNCollectM (Term lang Name)
termUNCollect = R.termTrimapM typeUNCollect return collectVar
  where
    collectVar :: R.Var Name (TermBase lang Name) -> UNCollectM (R.Var Name (TermBase lang Name))
    collectVar v = do
      case v of
        R.F (FreeName n) -> void $ unNameCollect n
        _                -> return ()
      return v

typeUNCollect :: PrtType lang -> UNCollectM (PrtType lang)
typeUNCollect = mapM collectVar
  where
    collectVar :: R.Var Name (TypeBase lang Name) -> UNCollectM (R.Var Name (TypeBase lang Name))
    collectVar v = do
      case v of
        R.F (TyFree n) -> void $ unNameCollect n
        _              -> return ()
      return v

defUNSubst :: Definition lang Name -> UNSubstM (Definition lang Name)
defUNSubst (DFunction r t ty) = DFunction r <$> termUNSubst t <*> typeUNSubst ty
defUNSubst (DConstructor i n) = DConstructor i <$> unNameSubst n
defUNSubst (DDestructor n)    = DDestructor <$> unNameSubst n
defUNSubst (DTypeDef n)       = DTypeDef <$> unTypeDefSubst n

unTypeDefSubst :: TypeDef lang Name -> UNSubstM (TypeDef lang Name)
unTypeDefSubst (Datatype k vs dest cons) =
  Datatype k <$> mapM (\(n, k) -> (,k) <$> unNameSubst n) vs
             <*> unNameSubst dest
             <*> mapM (\(n, ty) -> (,) <$> unNameSubst n <*> typeUNSubst ty) cons

unNameSubst :: Name -> UNSubstM Name
unNameSubst n = do
  muses <- asks (M.lookup $ nameString n)
  case muses of
    Just [_] -> return $ n { nameUnique = Nothing }
    -- xs cannot be empty: always insert a nameString with a non-empty set of Name
    Just xs  -> return $ n { nameUnique = L.elemIndex n xs }
    Nothing  -> return n

termUNSubst :: Term lang Name -> UNSubstM (Term lang Name)
termUNSubst = R.termTrimapM typeUNSubst return subst
  where
    subst :: R.Var Name (TermBase lang Name) -> UNSubstM (R.Var Name (TermBase lang Name))
    subst (R.F (FreeName n)) = R.F . FreeName <$> unNameSubst n
    subst x                  = return x

typeUNSubst :: PrtType lang -> UNSubstM (PrtType lang)
typeUNSubst = R.tyBimapM return subst
  where
    subst (R.F (TyFree n))  = R.F . TyFree <$> unNameSubst n
    subst x                 = return x

-- ** Utility Functions

safeIdx :: (Integral i) => [a] -> i -> Maybe a
safeIdx l = go l . fromIntegral
  where
    go []     _ = Nothing
    go (x:_)  0 = Just x
    go (_:xs) n = go xs (n-1)

unsafeIdx :: (Integral i) => String -> [a] -> i -> a
unsafeIdx lbl l = fromMaybe (error $ "unsafeIdx: out-of-bounds; " ++ lbl) . safeIdx l
