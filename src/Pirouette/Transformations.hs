-- |Implements whole-program transformations. If you're looking
-- for term transformations, check "Pirouette.Term.Transformations"
--
module Pirouette.Transformations where

import           Pirouette.Monad
import           Pirouette.Monad.Logger
import           Pirouette.Monad.Maybe
import           Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax.Subst
import           Pirouette.Term.Transformations

import qualified PlutusCore as P

import           Control.Monad.State
import qualified Data.List.NonEmpty as NE
import           Data.List (foldl')
import           Data.Maybe (mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Generics.Uniplate.Operations


-- |Removes all Even-Odd mutually recursive functions from the program.
-- When successfull, sets the 'tord' state field with a list of names indicating the order in which
-- they should be defined so that the dependencies of a term @T@ are defined before @T@.
elimEvenOddMutRec :: (MonadPirouette m) => m ()
elimEvenOddMutRec = gets (mapMaybe (uncurry funOrType) . M.toList . decls)
                >>= sortDeps
                >>= foldM (\res c -> (++ res) <$> elimDepCycles c) []
                >>= \ord -> modify (\st -> st { tord = Just ord })
 where
  -- Attempts to eliminate dependency cycles for a set of mutually recursive definitions.
  -- If successfull, returns a @ns@ containing the order in which the
  -- inputs should be declared. The declarations within the state monad will
  -- have been updated accordingly. Take the following situation:
  --
  -- > f x = op1 (f (x-1)) (g x)
  -- > g x = h x + 2
  -- > h x = f (x - 3)
  --
  -- Calling @elimDepCycles ["f", "g", "h"]@ will return @["f", "h", "g"]@ and
  -- will alter the definitions to:
  --
  -- > f x = op1 (f (x-1)) (f (x - 3) - 2)
  -- > h x = f (x - 3)
  -- > g x = h x + 2
  --
  elimDepCycles :: (MonadPirouette m) => NE.NonEmpty (R.Arg Name Name) -> m [R.Arg Name Name]
  elimDepCycles (e NE.:| []) = return [e]
  elimDepCycles (e NE.:| es) = pushCtx ("elimDepCycles " ++ show (e:es)) $ go (e:es)
    where
      snoc x xs = xs ++ [x]

      -- Because PlutusIR is not dependently typed, it should not be the case that
      -- terms depends on types or vice versa, hence, we should only have to deal with
      -- dependency classes that involve terms or types exclusively.
      go   [] = return []
      go d@(R.TyArg t : ts) = do
        unless (all R.isTyArg ts) $ throwError' $ PEOther "Mixed dependencies"
        logWarn "MutRec Types: TLA+ will error if BoundedSetOf is needed for any of these types."
        return d
      go d@(R.Arg n : ns) =
        case mapM R.fromArg d of
          Nothing -> throwError' $ PEOther "Mixed dependencies"
          Just as -> map R.Arg <$> solveTermDeps 0 as

      -- In order to break the cycle for a class of mutually dependend terms ds, we'll
      -- try to find a non-recursive term d and expand it in all terms in ds \ {d},
      -- then we repeat this until at most one term remains.
      --
      -- If this can't be done, we throw an error
      solveTermDeps _ []  = return []
      solveTermDeps _ [x] = return [x]
      solveTermDeps ctr nss@(n:ns)
        | ctr == length nss = throwError' $ PEMutRecDeps nss
        | otherwise = do
            isRec <- termIsRecursive n
            if isRec
            then solveTermDeps (ctr + 1) (ns ++ [n])
            else mapM_ (expandDefIn n) ns
              >> snoc n <$> solveTermDeps 0 ns

-- |Expand all non-recursive definitions in our state, keeping only the
-- recursive definitions or those satisfying the @keep@ predicate.
expandAllNonRec :: (MonadPirouette m) => (Name -> Bool) -> m ()
expandAllNonRec keep = do
  ds  <- gets decls
  ord <- dependencyOrder
  let (remainingNames, ds', _) = foldl' go ([], ds, M.empty) ord
  modify (\st -> st{ decls = ds' , tord = Just $ reverse remainingNames })
 where
  -- The 'go' functions goes over the defined terms in dependency order
  -- and inlines terms as much as possible. To do so efficiently,
  -- we keep a map of inlinable definitions and we also maintain the order
  -- for the names that are left in the actual definitions.
  --
  -- In general, say that: (rNs, ds', rest) = foldl' go ([], decls, M.empty) ord
  -- then, with a slight abuse of notation:
  --
  -- >    M.union ds' rest == decls -- module beta equivalence
  -- > && S.fromList rNs == S.fromList (M.keys ds')
  -- > && reverse rNs `isSubListOf` ord
  --
  go :: ([R.Arg Name Name], Decls Name P.DefaultFun, M.Map Name PrtTerm)
     -> R.Arg Name Name
     -> ([R.Arg Name Name], Decls Name P.DefaultFun, M.Map Name PrtTerm)
  go (names, currDecls, inlinableDecls) (R.TyArg ty) = (R.TyArg ty : names, currDecls, inlinableDecls)
  go (names, currDecls, inlinableDecls) (R.Arg k) =
    let (decls', kDef) = expandDefsIn inlinableDecls currDecls k
     in if R.Arg k `S.member` termNames kDef || keep k
        then (R.Arg k : names , decls'            , inlinableDecls)
        else (names           , M.delete k decls' , M.insert k kDef inlinableDecls)

  expandDefsIn :: M.Map Name PrtTerm
               -> Decls Name P.DefaultFun
               -> Name
               -> (Decls Name P.DefaultFun, PrtTerm)
  expandDefsIn inlinables decls k =
    case M.lookup k decls of
      Nothing -> error $ "expandDefsIn: term " ++ show k ++ " undefined in decls"
      Just (DFunction r t ty) ->
        let t' = rewrite (inlineAll inlinables) t
         in (M.insert k (DFunction r t' ty) decls, t')
      Just _  -> error $ "expandDefsIn: term " ++ show k ++ " not a function"

  inlineAll :: M.Map Name PrtTerm -> PrtTerm -> Maybe PrtTerm
  inlineAll inlinables (R.App (R.F (FreeName n)) args) = do
    nDef <- M.lookup n inlinables
    return . deshadowBoundNames $ R.appN nDef args
  inlineAll _ _ = Nothing
