{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Pirouette.Term.Syntax
  ( module EXPORT
  , PrtTerm, PrtType, PrtDef, PrtTypeDef, PrtArg
  , PrtVar, PrtTyVar
  , Name(..), ToName(..), TyName
  , separateBoundFrom
  , declsUniqueNames
  , safeIdx
  , unsafeIdx
  ) where

import           Pirouette.Term.Syntax.Base    as EXPORT
import           Pirouette.Term.Syntax.Pretty  as EXPORT
import qualified Pirouette.Term.Syntax.SystemF as R
import  Pirouette.Term.Syntax.Subst

import qualified PlutusCore                as P
import qualified PlutusCore.Pretty         as P (pretty)
import           Control.Monad.State
import           Control.Monad.Reader
import qualified Data.List                 as L
import qualified Data.Text                 as T
import qualified Data.Map.Strict           as M
import qualified Data.Set                  as S
import           Data.Data
import           Data.String
import           Data.Maybe (fromMaybe)

-- * Top Level Terms and Types
--
-- $toplvlterms
--
-- Pirouette terms and types are simply 'Term' and 'Type' with their type variables
-- instantiated.

type PrtTerm    = Term Name P.DefaultFun
type PrtType    = Type Name
type PrtArg     = R.Arg PrtType PrtTerm

type PrtDef     = Definition Name P.DefaultFun
type PrtTypeDef = TypeDef Name

type PrtVar     = R.Var Name (PIRBase P.DefaultFun Name)
type PrtTyVar   = R.Var Name (TypeBase Name)

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

instance ToName P.Name where
  toName pn = Name (P.nameString pn) (Just $ P.unUnique $ P.nameUnique pn)

instance ToName P.TyName where
  toName = toName . P.unTyName

instance Pretty P.DefaultFun where
  pretty = P.pretty

-- `separateBoundFrom u t` outputs `t` where all the bound variables occuring in both terms
-- are renamed to avoid name clashes.
separateBoundFrom :: Term Name fun -> Term Name fun -> Term Name fun
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
declsUniqueNames :: Decls Name fun -> Decls Name fun
declsUniqueNames = M.fromList . go . M.toList
  where
    onPairM f g (x, y) = (,) <$> f x <*> g y

    go :: [(Name, Definition Name fun)] -> [(Name , Definition Name fun)]
    go ds = let (_, ks) = flip runState M.empty
                          $ mapM (onPairM unNameCollect defUNCollect) ds
             in flip runReader (M.map S.toList ks)
              $ mapM (onPairM unNameSubst defUNSubst) ds

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

defUNCollect :: Definition Name fun -> UNCollectM (Definition Name fun)
defUNCollect (DFunction r t ty) = DFunction r <$> termUNCollect t <*> typeUNCollect ty
defUNCollect (DConstructor i n) = DConstructor i <$> unNameCollect n
defUNCollect (DDestructor n)    = DDestructor <$> unNameCollect n
defUNCollect (DTypeDef n)       = DTypeDef <$> unTypeDefCollect n

unTypeDefCollect :: TypeDef Name -> UNCollectM (TypeDef Name)
unTypeDefCollect d@(Datatype _ _ dest cons) = do
  void $ unNameCollect dest
  let (consNames, types) = unzip cons
  mapM_ unNameCollect consNames
  mapM_ typeUNCollect types
  return d

termUNCollect :: Term Name fun -> UNCollectM (Term Name fun)
termUNCollect = R.termTrimapM typeUNCollect return collectVar
  where
    collectVar :: R.Var Name (PIRBase fun Name) -> UNCollectM (R.Var Name (PIRBase fun Name))
    collectVar v = do
      case v of
        R.F (FreeName n) -> void $ unNameCollect n
        _                -> return ()
      return v

typeUNCollect :: PrtType -> UNCollectM PrtType
typeUNCollect = mapM collectVar
  where
    collectVar :: R.Var Name (TypeBase Name) -> UNCollectM (R.Var Name (TypeBase Name))
    collectVar v = do
      case v of
        R.F (TyFree n) -> void $ unNameCollect n
        _              -> return ()
      return v

defUNSubst :: Definition Name fun -> UNSubstM (Definition Name fun)
defUNSubst (DFunction r t ty) = DFunction r <$> termUNSubst t <*> typeUNSubst ty
defUNSubst (DConstructor i n) = DConstructor i <$> unNameSubst n
defUNSubst (DDestructor n)    = DDestructor <$> unNameSubst n
defUNSubst (DTypeDef n)       = DTypeDef <$> unTypeDefSubst n

unTypeDefSubst :: TypeDef Name -> UNSubstM (TypeDef Name)
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

termUNSubst :: Term Name fun -> UNSubstM (Term Name fun)
termUNSubst = R.termTrimapM typeUNSubst return subst
  where
    subst :: R.Var Name (PIRBase fun Name) -> UNSubstM (R.Var Name (PIRBase fun Name))
    subst (R.F (FreeName n)) = R.F . FreeName <$> unNameSubst n
    subst x                  = return x

typeUNSubst :: PrtType -> UNSubstM PrtType
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
