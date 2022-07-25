{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.DCE where

import Control.Arrow (second)
import Data.Generics.Uniplate.Data
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils

data CtorRemoveInfo = CtorRemoveInfo
  { criCtorTypeName :: Name
  , criCtorName :: Name
  , criCtorIdx :: Int
  , criDtorName :: Name
  } deriving (Show, Eq, Ord)

newtype RemoveDeadCtorsOpts = RemoveDeadCtorsOpts
  { rdcoCanRemove :: M.Map T.Text [T.Text]
  } deriving (Show)

-- * Dead constructors elimination

removeDeadCtors :: forall lang. (Language lang)
                => RemoveDeadCtorsOpts
                -> PrtUnorderedDefs lang
                -> PrtUnorderedDefs lang
removeDeadCtors RemoveDeadCtorsOpts{..} defs = L.foldl' (flip removeCtor) defs ctorsToRemove
  where
    ctorsToRemove = filter canRemove $ findDeadCtors defs

    canRemove CtorRemoveInfo{..}
      | Just tyRemoveList <- nameString criCtorTypeName `M.lookup` rdcoCanRemove = nameString criCtorName `elem` tyRemoveList
    -- If we don't have any record for the type, we keep its constructors unconditionally:
    -- removal of a type's constructors should be a very conscious and explicit decision by the user.
    canRemove _ = False

-- | Finds the constructors that aren't used in the program.
--
-- Returns them in the reverse order of appearance in each individual data type.
-- This ordering allows removing constructors one after another, since each removed ctor
-- won't shift/invalidate the indexes of the subsequent ones.
findDeadCtors :: forall lang. (Language lang) => PrtUnorderedDefs lang -> [CtorRemoveInfo]
findDeadCtors defs = L.sortOn (negate . criCtorIdx) $ M.elems unusedCtors
  where
    ctorNameMap = M.fromList [ ((tyName, idx), ctorName)
                             | ((_, ctorName), DConstructor idx tyName) <- M.toList $ prtUODecls defs
                             ]
    allCtors = M.fromList [ (ctorName, CtorRemoveInfo{..})
                          | ((_, criCtorTypeName), DTypeDef td) <- M.toList $ prtUODecls defs
                          , let criDtorName = destructor td
                          , (criCtorIdx, (ctorName, _)) <- zip [0..] $ constructors td
                          , let criCtorName = ctorNameMap M.! (criCtorTypeName, criCtorIdx)
                          ]
    usedNames = S.fromList [ name | TermSig name <- universeBi defs :: [TermBase lang] ]
    unusedCtors = M.filterWithKey (\ctorName _ -> ctorName `S.notMember` usedNames) allCtors

-- | Removes the constructor with the given index of the given type from the program.
--
-- This removes both the constructor definition as well as
-- the corresponding branches in the calls to the type's destructor.
-- This also updates the definitions for the subsequent constructors to have the right (decremented) index.
removeCtor :: forall lang. (Language lang)
           => CtorRemoveInfo
           -> PrtUnorderedDefs lang
           -> PrtUnorderedDefs lang
removeCtor CtorRemoveInfo{..} = updateMatchers . shiftSubsequentCtorsDefs . updateTypeDef . removeCtorDef
  where
    removeCtorDef defs = defs {prtUODecls = M.filter (/= DConstructor criCtorIdx criCtorTypeName) $ prtUODecls defs}

    updateTypeDef defs = defs {prtUODecls = fixup <$> prtUODecls defs}
      where
        fixup (DTypeDef td)
          | destructor td == criDtorName = DTypeDef td {constructors = removeAt criCtorIdx $ constructors td}
        fixup d = d

    shiftSubsequentCtorsDefs defs = defs {prtUODecls = shiftCtor <$> prtUODecls defs}
      where
        shiftCtor (DConstructor idx name)
          | name == criCtorTypeName && idx > criCtorIdx = DConstructor (idx - 1) name
        shiftCtor d = d

    updateMatchers defs = transformBi removeCase defs
    removeCase :: Term lang -> Term lang
    removeCase (SystF.App (SystF.Free (TermSig name)) args)
      | name == criDtorName = SystF.App (SystF.Free (TermSig name)) $ prefix <> removeAt criCtorIdx cases
      where
        (prefix, cases) = splitArgsTermsTail args
    removeCase t = t

-- * Dead fields elimination

removeDeadFields :: forall lang. (Language lang)
                 => PrtUnorderedDefs lang
                 -> PrtUnorderedDefs lang
removeDeadFields defs = L.foldl' removeDfInType defs types
  where
    types = [ td | DTypeDef td <- M.elems $ prtUODecls defs ]

removeDfInType :: forall lang. (Language lang)
               => PrtUnorderedDefs lang
               -> TypeDef lang
               -> PrtUnorderedDefs lang
removeDfInType defs ty@Datatype{..} = L.foldl' (removeDfInTypeCtor ty) defs [0 .. fromIntegral $ length constructors - 1]

removeDfInTypeCtor :: forall lang. (Language lang)
                   => TypeDef lang
                   -> PrtUnorderedDefs lang
                   -> Integer
                   -> PrtUnorderedDefs lang
removeDfInTypeCtor ty defs ctorIdx = PrtUnorderedDefs
                                   $ transformBi updateDtor
                                   $ updateCtor <$> prtUODecls defs
  where
    ctor = constructors ty !! fromIntegral ctorIdx
    fieldsIdxes = unusedFields defs ty ctorIdx
    (flatArgs, res) = flattenType $ snd ctor

    updateCtor (DTypeDef other) | destructor other == destructor ty = DTypeDef ty {constructors = ctors'}
      where
        ctor' = (fst ctor, unflattenType (removeAts fieldsIdxes flatArgs) res)
        ctors' = updateAt ctorIdx (constructors ty) ctor'
    updateCtor def = def

    updateDtor :: Term lang -> Term lang
    updateDtor (SystF.App (SystF.Free (TermSig dtorName)) dtorArgs)
      | dtorName == destructor ty = SystF.App (SystF.Free (TermSig dtorName)) $ prefix <> branches'
      where
        (prefix, branches) = splitArgsTermsTail dtorArgs
        branches' = updateAt ctorIdx branches branch'
        branch' = SystF.argMap id (dropArgs fieldsIdxes) $ branches !! fromIntegral ctorIdx
    updateDtor x = x

-- | Tries to remove a single bound variable with the given index from a function.
-- If the argument isn't used, it just decrements the indices of further arguments.
-- If it's used, it fails, returning @Nothing@.
--
-- If the index @i@ is non-negative,
-- then the variables pointing to the @i@th bound variable are attempted to be removed.
-- If it's negative, then the lambda abstraction with the index @-i - 1@ (from the left)
-- is attempted to be removed, as long as its binder isn't used.
--
-- This is better illustrated by an example. Consider
--
-- > λ Ty0. λ Ty1. λ Ty2. foo #0 #2 #4
--
-- so @#0@ points to the @Ty2@, @#2@ points ot the @Ty0@, and @#4@ points to the
-- @4 - 3 = 1@st variable in the context.
--
-- Then:
-- * @tryDropArg 1@ fails, since it sees that the variable is used via the @#4@.
-- * @tryDropArg 0@ suceeds, and the resulting term would be @λ Ty0. λ Ty1. λ Ty2. foo #0 #2 #3@
--   (note the index decremented).
-- * @tryDropArg (-1)@  fails, since it tries to remove the first abstraction (with the @Ty0@),
--   which is used via @#2@.
-- * @tryDropArg (-2)@  succeeds, resulting in @λ Ty0. λ Ty2. foo #0 #1 #3@.
tryDropArg :: Integer
           -> Term lang
           -> Maybe (Term lang)
tryDropArg (-1) (SystF.Lam _ _ body) = tryDropArg 0 body
tryDropArg (-1) (SystF.Abs _ _ body) = tryDropArg 0 body
tryDropArg argIdx (SystF.App var args) = SystF.App <$> var' <*> args'
  where
    var'
      | SystF.Bound ann idx <- var =
        case idx `compare` argIdx of
             -- the current var's idx is less than the argument we're removing, keep it as is
             LT -> Just var
             -- the argument is actually used, can't remove it
             EQ -> Nothing
             -- the current var's idx is greater than the argument we're removing,
             -- decrement it to account for the argument removal
             GT -> Just $ SystF.Bound ann (idx - 1)
      | otherwise = Just var
    args' = mapM (SystF.argElim (Just . SystF.TyArg) (fmap SystF.TermArg . tryDropArg argIdx)) args
tryDropArg argIdx (SystF.Lam ann t body) = SystF.Lam ann t <$> tryDropArg (argIdx + 1) body
tryDropArg argIdx (SystF.Abs ann k body) = SystF.Abs ann k <$> tryDropArg (argIdx + 1) body

dropArgs :: [Integer]
         -> Term lang
         -> Term lang
dropArgs argsIxes term = foldr (\ix t -> fromJust $ tryDropArg ix t) term argsIxes

isArgUsed :: Integer
          -> Term lang
          -> Bool
isArgUsed argIdx term = isNothing $ tryDropArg argIdx term

isFieldUsed :: forall lang. (Language lang)
            => PrtUnorderedDefs lang
            -> Name     -- ^ destructor
            -> Integer  -- ^ constructor idx
            -> Integer  -- ^ field idx
            -> Bool
isFieldUsed defs matcher ctorIdx fieldIdx = any (isArgUsed fieldIdx) ctorBranches
  where
    ctorBranches = [ ctorBranch
                   | SystF.App (SystF.Free (TermSig name)) args <- universeBi defs :: [Term lang]
                   , name == matcher
                   , let SystF.TermArg ctorBranch = snd (splitArgsTermsTail args) !! fromIntegral ctorIdx
                   ]

-- | Returns the indices of the fields in the given ctor of a given type
-- that are unused in the whole program.
--
-- The returned list is sorted in asc order.
unusedFields :: forall lang. (Language lang)
             => PrtUnorderedDefs lang
             -> TypeDef lang
             -> Integer    -- ^ the constructor index
             -> [Integer]
unusedFields defs Datatype{..} ctorIdx =
  [ fieldIdx
  | fieldIdx <- [0 .. fieldsCnt - 1]
  , not $ isFieldUsed defs destructor ctorIdx (fieldIdx - fieldsCnt)
  ]
  where
    fieldsCnt = L.genericLength $ fst $ flattenType $ snd $ constructors !! fromIntegral ctorIdx

-- * Misc utils

removeAt :: Integral ix => ix -> [a] -> [a]
removeAt pos = uncurry (<>) . second tail . splitAt (fromIntegral pos)

removeAts :: Integral ix => [ix] -> [a] -> [a]
removeAts = go 0
  where
    go _ [] xs = xs
    go _ _  [] = error "removeAts: empty remainder"
    go curIdx (ix:ixes) (x:xs)
      | curIdx == ix = go (curIdx + 1) ixes xs
      | otherwise = x : go (curIdx + 1) (ix:ixes) xs

updateAt :: Integral ix => ix -> [a] -> a -> [a]
updateAt pos xs x = prefix <> (x : tail suffix)
  where
    (prefix, suffix) = splitAt (fromIntegral pos) xs
