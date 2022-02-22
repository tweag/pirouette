{-# LANGUAGE TupleSections #-}

module Pirouette.Term.Syntax
  ( module EXPORT
  , separateBoundFrom
  , declsUniqueNames
  , safeIdx
  , unsafeIdx
  ) where

import           Pirouette.Term.Syntax.Base    as EXPORT
import           Pirouette.Term.Syntax.Pretty  as EXPORT
import qualified Pirouette.Term.Syntax.SystemF as Raw
import  Pirouette.Term.Syntax.Subst

import           Control.Monad.State
import           Control.Monad.Reader
import Data.Bifunctor (first)
import qualified Data.List                 as List
import qualified Data.Text                 as Text
import qualified Data.Map.Strict           as Map
import qualified Data.Set                  as Set
import           Data.Data
import           Data.String
import           Data.Maybe (fromMaybe)
import Pirouette.Term.Syntax.Pretty.Class
import Data.Void
import Control.Monad.Identity

-- | @separateBoundFrom u t@ outputs @t@ where all the bound variables occuring in both terms
-- are renamed to avoid name clashes when outputting code that relies on user given names
-- while still being able to use something close to the programmer-given names for the
-- generated code.
separateBoundFrom :: Term builtins -> Term builtins -> Term builtins
separateBoundFrom u t =
  let boundOf = Raw.termAnnFold Set.singleton in
  let inter = Set.intersection (boundOf u) (boundOf t) in
  if null inter
  then t
  else
    -- `structuredInter` transforms the set of name clashes into a map
    -- from nameString to the list of nameUnique associated.
    let structuredInter =
          Set.fold
            (\n m -> Map.insertWith (++) (nameString n) [nameUnique n] m)
            Map.empty
            inter
    in
    -- `nextFresh s txt i n` takes a set `s` of names and a `nameString` `txt` and outputs
    -- the first index which does not create clash.
    -- `n` starts from 0 and increases until a number not already taken is met,
    -- whereas `i` counts how much new number must be met.
    -- The purpose of `i` is to avoid to rename identically `x0` and `x1`
    -- if both are subject to name clash.
    let nextFresh :: Set.Set Name -> Text.Text -> Int -> Int -> Name
        nextFresh s txt i n
          | Set.member (Name txt (Just n)) s = nextFresh s txt i (n + 1)
          | i == 0 = Name txt (Just n)
          | otherwise = nextFresh s txt (i - 1) (n + 1)
    in
    let rename :: Map.Map Text.Text [Maybe Int] -> Set.Set Name -> Name -> Name
        rename m s n@(Name txt u) =
          case Map.lookup txt m of
            Nothing -> n
            Just x ->
              case List.elemIndex u x of
                Nothing -> n
                Just i -> nextFresh s txt i 0
    in
    let f = rename structuredInter (Set.union (boundOf u) (boundOf t)) in
    Raw.termTrimap id f (annMap f) t


-- ** Uniquely Naming
--
-- $uniquenames
--
-- Defines a number of functions for removing all the unnecessary 'nameUnique' parts.
-- This not only enables us to ignore De Bruijn indices in future steps, but produces
-- far more readable TLA+ code.
--
-- Worth noting that even though PlutusIR is guaranteed to have unique names as of now,
-- because we're normalizing terms, its better to do so with De Bruijn indices. Moreover,
-- it makes sure we don't need to worry about alpha equivalence of terms.
-- Finally, it happened before that we couldn't trust the pretty printer:
-- https://github.com/input-output-hk/plutus/issues/3445

-- |Exported interface function to uniquely naming declarations.
declsUniqueNames :: Decls builtins -> Term builtins -> (Decls builtins, Term builtins)
declsUniqueNames decls mainFun = first Map.fromList (go (Map.toList decls) mainFun)
  where
    onPairM f g (x, y) = (,) <$> f x <*> g y

    go :: [(Name, Definition builtins)] -> Term builtins
       -> ([(Name, Definition builtins)], Term builtins)
    go ds mainFun =
      let (_, ks) =
            flip runState Map.empty $ mapM (onPairM unNameCollect defUNCollect) ds
      in
      runReader
        (onPairM (mapM (onPairM unNameSubst defUNSubst)) termUNSubst (ds, mainFun))
        (Map.map Set.toList ks)

-- *** Auxiliar Definitions for Unique Naming
--
-- $uniquenamesaux
--
-- The unique naming algorithm is simple: we collect all names used in a map
-- from their nameString to the set of names that are used and share the same
-- nameString. We then convert those sets to lists and substitute names accordingly.
-- If a name shares no nameString with no other name, we ignore nameUnique.

type UNCollectM = State (Map.Map Text.Text (Set.Set Name))
type UNSubstM   = Reader (Map.Map Text.Text [Name])

-- We use 'flip S.union' because S.union is more efficient on S.union bigset smallset
-- and 'M.insertWith f k x' applies 'f x old_value' when there is a collision; hence,
-- old_value will be the larger set.
unNameCollect :: Name -> UNCollectM Name
unNameCollect n = modify (Map.insertWith (flip Set.union) (nameString n) (Set.singleton n)) >> return n

defUNCollect :: Definition builtins -> UNCollectM (Definition builtins)
defUNCollect (DFunction r t ty) = DFunction r <$> termUNCollect t <*> typeUNCollect ty
defUNCollect (DConstructor i n) = DConstructor i <$> unNameCollect n
defUNCollect (DDestructor n)    = DDestructor <$> unNameCollect n
defUNCollect (DTypeDef n)       = DTypeDef <$> unTypeDefCollect n

unTypeDefCollect :: TypeDef builtins -> UNCollectM (TypeDef builtins)
unTypeDefCollect d@(Datatype _ _ dest cons) = do
  void $ unNameCollect dest
  let (consNames, types) = unzip cons
  mapM_ unNameCollect consNames
  mapM_ typeUNCollect types
  return d

termUNCollect :: Term builtins -> UNCollectM (Term builtins)
termUNCollect = Raw.termTrimapM typeUNCollect return collectVar
  where
    collectVar :: Raw.Var Name (TermBase builtins) -> UNCollectM (Raw.Var Name (TermBase builtins))
    collectVar v = do
      case v of
        Raw.Free (TermFromSignature n) -> void $ unNameCollect n
        _                -> return ()
      return v

typeUNCollect :: Type builtins -> UNCollectM (Type builtins)
typeUNCollect = mapM collectVar
  where
    collectVar :: Raw.Var Name (TypeBase builtins) -> UNCollectM (Raw.Var Name (TypeBase builtins))
    collectVar v = do
      case v of
        Raw.Free (TypeFromSignature n) -> void $ unNameCollect n
        _              -> return ()
      return v

defUNSubst :: Definition builtins -> UNSubstM (Definition builtins)
defUNSubst (DFunction r t ty) = DFunction r <$> termUNSubst t <*> typeUNSubst ty
defUNSubst (DConstructor i n) = DConstructor i <$> unNameSubst n
defUNSubst (DDestructor n)    = DDestructor <$> unNameSubst n
defUNSubst (DTypeDef n)       = DTypeDef <$> unTypeDefSubst n

unTypeDefSubst :: TypeDef builtins -> UNSubstM (TypeDef builtins)
unTypeDefSubst (Datatype k vs dest cons) =
  Datatype k <$> mapM (\(n, k) -> (,k) <$> unNameSubst n) vs
             <*> unNameSubst dest
             <*> mapM (\(n, ty) -> (,) <$> unNameSubst n <*> typeUNSubst ty) cons

unNameSubst :: Name -> UNSubstM Name
unNameSubst n = do
  muses <- asks (Map.lookup $ nameString n)
  case muses of
    Just [_] -> return $ n { nameUnique = Nothing }
    -- xs cannot be empty: always insert a nameString with a non-empty set of Name
    Just xs  -> return $ n { nameUnique = List.elemIndex n xs }
    Nothing  -> return n

termUNSubst :: Term builtins -> UNSubstM (Term builtins)
termUNSubst = Raw.termTrimapM typeUNSubst return subst
  where
    subst :: Raw.Var Name (TermBase builtins) -> UNSubstM (Raw.Var Name (TermBase builtins))
    subst (Raw.Free (TermFromSignature n)) = Raw.Free . TermFromSignature <$> unNameSubst n
    subst x                  = return x

typeUNSubst :: Type builtins -> UNSubstM (Type builtins)
typeUNSubst = Raw.tyBimapM return subst
  where
    subst (Raw.Free (TypeFromSignature n))  = Raw.Free . TypeFromSignature <$> unNameSubst n
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
