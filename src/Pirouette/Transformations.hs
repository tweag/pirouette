{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Implements whole-program transformations. If you're looking
--  for term transformations, check "Pirouette.Term.Transformations"
module Pirouette.Transformations where

import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Generics.Uniplate.Operations
import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Pirouette.Monad
import Pirouette.Monad.Logger
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Term.Transformations
import Pirouette.Term.TransitiveDeps

-- | Removes all Even-Odd mutually recursive functions from the program.
--  When successfull, sets the 'tord' state field with a list of names indicating the order in which
--  they should be defined so that the dependencies of a term @T@ are defined before @T@.
elimEvenOddMutRec :: forall lang m. (LanguageBuiltins lang, PirouetteBase m) => PrtUnorderedDefs lang -> m (PrtOrderedDefs lang)
elimEvenOddMutRec udefs = do
  ordWithCycles <- runReaderT sortAllDeps udefs
  (ord, udefs') <- runStateT (foldM (\res c -> (++ res) <$> elimDepCycles c) [] ordWithCycles) udefs
  return $ prtOrderedDefs udefs' ord
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
    elimDepCycles ::
      (LanguageBuiltins lang, PirouetteBase m) =>
      NonEmpty (SystF.Arg Name Name) ->
      StateT (PrtUnorderedDefs lang) m [SystF.Arg Name Name]
    elimDepCycles (e :| []) = return [e]
    elimDepCycles (e :| es) = pushCtx ("elimDepCycles " ++ show (e : es)) $ go (e : es)
      where
        snoc x xs = xs ++ [x]

        -- Because PlutusIR is not dependently typed, it should not be the case that
        -- terms depends on types or vice versa, hence, we should only have to deal with
        -- dependency classes that involve terms or types exclusively.
        go [] = return []
        go d@(SystF.TyArg t : ts) = do
          unless (all SystF.isTyArg ts) $ throwError' $ PEOther "Mixed dependencies"
          logWarn "MutRec Types: TLA+ will error if BoundedSetOf is needed for any of these types."
          return d
        go d@(SystF.TermArg n : ns) =
          case mapM SystF.fromArg d of
            Nothing -> throwError' $ PEOther "Mixed dependencies"
            Just as -> map SystF.TermArg <$> solveTermDeps 0 as

        -- In order to break the cycle for a class of mutually dependend terms ds, we'll
        -- try to find a non-recursive term d and expand it in all terms in ds \ {d},
        -- then we repeat this until at most one term remains.
        --
        -- If this can't be done, we throw an error
        solveTermDeps _ [] = return []
        solveTermDeps _ [x] = return [x]
        solveTermDeps ctr nss@(n : ns)
          | ctr == length nss = throwError' $ PEMutRecDeps nss
          | otherwise = do
            isRec <- termIsRecursive n
            if isRec
              then solveTermDeps (ctr + 1) (ns ++ [n])
              else
                mapM_ (expandDefInSt n) ns
                  >> snoc n <$> solveTermDeps 0 ns

        expandDefInSt :: Name -> Name -> StateT (PrtUnorderedDefs lang) m ()
        expandDefInSt n m = do
          defn <- prtTermDefOf n
          modify (\st -> st {prtUODecls = fst $ expandDefsIn (Map.singleton n defn) (prtUODecls st) m})

-- | Expand all non-recursive definitions in our state, keeping only the
--  recursive definitions or those satisfying the @keep@ predicate.
expandAllNonRec :: forall lang. (LanguageBuiltins lang) => (Name -> Bool) -> PrtOrderedDefs lang -> PrtOrderedDefs lang
expandAllNonRec keep prtDefs =
  let ds = prtDecls prtDefs
      ord = prtDepOrder prtDefs
      (remainingNames, ds', inlinables) = foldl' go ([], ds, Map.empty) ord
      mainTerm = rewrite (inlineAll inlinables) $ prtMainTerm prtDefs
   in PrtOrderedDefs ds' (reverse remainingNames) mainTerm
  where
    -- The 'go' functions goes over the defined terms in dependency order
    -- and inlines terms as much as possible. To do so efficiently,
    -- we keep a map of inlinable definitions and we also maintain the order
    -- for the names that are left in the actual definitions.
    --
    -- In general, say that: (rNs, ds', rest) = foldl' go ([], decls, Map.empty) ord
    -- then, with a slight abuse of notation:
    --
    -- >    Map.union ds' rest == decls -- module beta equivalence
    -- > && Set.fromList rNs == Set.fromList (Map.keys ds')
    -- > && reverse rNs `isSubListOf` ord
    --
    go ::
      ([SystF.Arg Name Name], Decls lang, Map.Map Name (Term lang)) ->
      SystF.Arg Name Name ->
      ([SystF.Arg Name Name], Decls lang, Map.Map Name (Term lang))
    go (names, currDecls, inlinableDecls) (SystF.TyArg ty) = (SystF.TyArg ty : names, currDecls, inlinableDecls)
    go (names, currDecls, inlinableDecls) (SystF.TermArg k) =
      let (decls', kDef) = expandDefsIn inlinableDecls currDecls k
       in if SystF.TermArg k `Set.member` termNames kDef || keep k
            then (SystF.TermArg k : names, decls', inlinableDecls)
            else (names, Map.delete k decls', Map.insert k kDef inlinableDecls)

expandDefsIn ::
  (LanguageBuiltins lang) =>
  Map.Map Name (Term lang) ->
  Decls lang ->
  Name ->
  (Decls lang, Term lang)
expandDefsIn inlinables decls k =
  case Map.lookup k decls of
    Nothing -> error $ "expandDefsIn: term " ++ show k ++ " undefined in decls"
    Just (DFunction r t ty) ->
      let t' = deshadowBoundNames $ rewrite (inlineAll inlinables) t
       in (Map.insert k (DFunction r t' ty) decls, t')
    Just _ -> error $ "expandDefsIn: term " ++ show k ++ " not a function"

inlineAll :: Map.Map Name (Term lang) -> Term lang -> Maybe (Term lang)
inlineAll inlinables (SystF.App (SystF.Free (TermFromSignature n)) args) = do
  nDef <- Map.lookup n inlinables
  Just $ SystF.appN nDef args
inlineAll _ _ = Nothing

-- ** Sanity Checks

-- | Checks that all deBruijn indices make sense, this gets run whenever pirouette
--  is ran with the @--sanity-check@ flag.
checkDeBruijnIndices :: (PirouetteReadDefs lang m, PrettyLang lang) => m ()
checkDeBruijnIndices = pushCtx "checkDeBruijn" $ do
  allDefs <- prtAllDefs
  forM_ (Map.toList allDefs) $ \(n, def) -> do
    case defTermMapM (\t -> go 0 0 t >> return t) def of
      Left err ->
        logError ("Invalid de Bruijn index for " ++ show n ++ "; " ++ show err)
          >> logError (renderSingleLineStr (pretty def))
          >> throwError' (PEOther "Invalid de Bruijn index")
      Right _ -> return ()
  where
    go :: Integer -> Integer -> Term lang -> Either String ()
    go ty term (SystF.Lam (SystF.Ann ann) _ t) =
      go ty (term + 1) t
    go ty term (SystF.Abs (SystF.Ann ann) _ t) =
      go (ty + 1) term t
    go ty term (SystF.App n args) = do
      mapM_ (SystF.argElim (const $ return ()) (go ty term)) args
      case n of
        SystF.Bound _ i ->
          when (i >= term) $
            Left $ "Referencing var " ++ show i ++ " with only " ++ show term ++ " lams"
        _ -> return ()
