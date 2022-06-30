{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Re-exports all the transformations available in Pirouette.
--  Most of the transformations are whole-program transformations,
--  with the exception of those within "Pirouette.Transformations.Term".
module Pirouette.Transformations
  ( module X,
    checkDeBruijnIndices,
  )
where

import Control.Monad.Identity
import qualified Data.Map as Map
import Pirouette.Monad
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Contextualize as X
import Pirouette.Transformations.Defunctionalization as X
import Pirouette.Transformations.ElimEvenOddMutRec as X
import Pirouette.Transformations.EtaExpand as X
import Pirouette.Transformations.Inline as X
import Pirouette.Transformations.Monomorphization as X
import Pirouette.Transformations.Prenex as X
import Pirouette.Transformations.Term as X

-- ** Sanity Checks

-- | Checks that all deBruijn indices make sense, this gets run whenever pirouette
--  is ran with the @--sanity-check@ flag.
checkDeBruijnIndices :: (PirouetteReadDefs lang m, LanguagePretty lang) => m ()
checkDeBruijnIndices = do
  allDefs <- prtAllDefs
  forM_ (Map.toList allDefs) $ \(_, def) -> do
    case defTermMapM (\t -> go 0 0 t >> return t) def of
      Left err -> prtError $ PEOther $ "Invalid de Bruijn index" ++ show err
      Right _ -> return ()
  where
    go :: Integer -> Integer -> Term lang -> Either String ()
    go ty term (SystF.Lam (SystF.Ann _ann) _ t) =
      go ty (term + 1) t
    go ty term (SystF.Abs (SystF.Ann _ann) _ t) =
      go (ty + 1) term t
    go ty term (SystF.App n args) = do
      mapM_ (SystF.argElim (const $ return ()) (go ty term)) args
      case n of
        SystF.Bound _ i ->
          when (i >= term) $
            Left $ "Referencing var " ++ show i ++ " with only " ++ show term ++ " lams"
        _ -> return ()
