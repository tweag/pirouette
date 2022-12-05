{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Runner where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Default
import qualified Data.List as L
import qualified Data.Map as M
import Data.String
import Data.Tuple.Extra
import Pirouette
import Pirouette.Monad
import Pirouette.Symbolic.Eval hiding (Options)
import qualified Pirouette.Symbolic.Eval as P (Options)
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Term.TypeChecker
import Pirouette.Transformations
import Test.Tasty.HUnit

-- | Set of options to control the particular run of pirouette
type DumpingStages lang = (Language lang, LanguageBuiltinTypes lang) => FilePath -> Stages (PrtUnorderedDefs lang) (PrtOrderedDefs lang)

data RunOptions = RunOptions
  { optsPirouette :: P.Options,
    optsDumpIntermediate :: Maybe ([String], FilePath),
    optsStages :: forall lang. DumpingStages lang
  }

instance Default RunOptions where
  def = RunOptions def Nothing pirouetteBoundedSymExecStages

runPirouette ::
  (Language lang, LanguagePrelude lang, LanguageBuiltinTypes lang, LanguageSymEval lang) =>
  RunOptions ->
  PrtUnorderedDefs lang ->
  AssumeProve lang ->
  Term lang ->
  Decls lang ->
  IO ()
runPirouette opts (PrtUnorderedDefs augments) (toAssume :==>: toProve) main0 preDecls = do
  let PrtUnorderedDefs decls0 = complementWithBuiltinPrelude $ PrtUnorderedDefs preDecls

  -- first we contextualize the user declarations, making sure they will refer to their right
  -- counterparts in  @decls0@.
  let augments' = runReader (contextualizeDecls augments) (PrtUnorderedDefs decls0)
  -- Now we try to remove as many 'nameUnique' bits as possible, to help with writing
  -- predicates and referring to types.
  let (decls1, main) = (augments' `M.union` decls0, main0)

  -- PrtUnorderedDefs decls1 = prenex $ PrtUnorderedDefs decls0'
  -- TODO: what if we don't manage to infer the type of main? Also, can't we make this interface much better? These empty lists are awkward here.
  let Right (Just mainTy) = runExcept $ runReaderT (typeInferTerm main) ((decls1, []), [])
  let mainName = fromString "__main"
  let mainDef = DFunDef FunDef {funIsRec = NonRec, funBody = main, funTy = mainTy}
  let (mainTyArgs, mainTyRes) = SystF.tyFunArgs mainTy

  -- If @main :: Parms -> Datum -> Redeemer -> Ctx -> RES@, then the type of our toAssume and toProve terms is:
  --
  -- > RES -> Parms -> Datum -> Redeemer -> Bool
  --
  let tBool = SystF.TyPure . SystF.Free . TySig $ fromString "Bool"
  let ty = SystF.TyFun tBool (foldr SystF.TyFun tBool mainTyArgs)

  -- Because we might use higher order or polymorphic functions in our assume and prove definitons, we will actually reify
  -- them into definitions and put them in the context, this will make sure that we will transform them accordingly
  let assumeName = fromString "__toAssume"
  let assumeTerm = runReader (contextualizeTerm toAssume) (PrtUnorderedDefs decls1)
  let assumeDef = DFunDef FunDef {funIsRec = NonRec, funBody = assumeTerm, funTy = ty}

  let proveName = fromString "__toProve"
  let proveTerm = runReader (contextualizeTerm toProve) (PrtUnorderedDefs decls1)
  let proveDef = DFunDef FunDef {funIsRec = NonRec, funBody = proveTerm, funTy = ty}

  -- The final declarations are:
  let decls =
        M.insert (TermNamespace, mainName) mainDef $
          M.insert (TermNamespace, assumeName) assumeDef $
            M.insert (TermNamespace, proveName) proveDef decls1

  -- At this point, we're almost ready to call the prover. It does help tp ensure that our
  -- definitions are type-correct, though!
  case typeCheckDecls decls of
    Left tyerr -> assertFailure $ show $ pretty tyerr
    Right _ -> do
      let fpath = maybe "" snd $ optsDumpIntermediate opts
      let dump = fst <$> optsDumpIntermediate opts
      orderedDecls <- runStages dump (optsStages opts fpath) (PrtUnorderedDefs decls)
      (res, stats) <- flip runReaderT orderedDecls $ do
        fn' <- prtTermDefOf mainName
        assume' <- prtTermDefOf assumeName
        toProve' <- prtTermDefOf proveName
        proveAnyAccum (optsPirouette opts) isCounter (Problem mainTyRes fn' assume' toProve')
      case res of
        Just Path {pathResult = CounterExample t model} -> do
          case model of
            Model [] -> assertFailure $ "Stuck at:\n" ++ show (pretty t)
            _ -> assertFailure $ "Counterexample:\n" ++ show (pretty model)
        Just _ -> error "Should never happen"
        Nothing -> print stats -- success, no counter found anywhere.
  where
    isCounter Path {pathResult = CounterExample _ _, pathStatus = s}
      | s /= OutOfFuel = True
    isCounter _ = False

{- ORMOLU_DISABLE -}
-- | Defines the stages a pirouette program goes through; the first stage is the identidy to enable us
--  to easily print the set of definitions that come from translating a PlutusIR program into a
--  pirouette one, before the set of definitions that happen in between.
pirouetteBoundedSymExecStages :: forall lang. DumpingStages lang
pirouetteBoundedSymExecStages fpath =
  Comp "init" id dumpUDefs $
  Comp "rm-excessive-destr" removeExcessiveDestArgs' dumpUDefs $
  Comp "monomorphize" monomorphize dumpUDefs $
  Comp "defunctionalize" defunctionalize dumpUDefs $
  Comp "cycle-elim" elimEvenOddMutRec dumpOrdDefs
  Id
  where
    typecheck :: String -> Decls lang -> IO ()
    typecheck stageName prog =
      case typeCheckDecls prog of
        Left tyerr -> assertFailure ("Result of stage " ++ stageName ++ " has type errors:\n" ++ show (pretty tyerr))
        Right _ -> return ()

    dumpUDefs :: String -> PrtUnorderedDefs lang -> IO ()
    dumpUDefs stageName (PrtUnorderedDefs prog) = do
      writeFile (fpath ++ "-" ++ stageName) $ show $ pretty prog
      typecheck stageName prog

    -- Similar to dumpUDefs, but dumps things in order
    dumpOrdDefs :: String -> PrtOrderedDefs lang -> IO ()
    dumpOrdDefs stageName (PrtOrderedDefs prog ord) = do
      let ordProg = map (\arg -> runReader (prtDefOf (argNamespace arg) (argName arg)) (PrtUnorderedDefs prog)) ord
      writeFile (fpath ++ "-" ++ stageName) $ show $ pretty ordProg
      typecheck stageName prog
      where
        argNamespace = SystF.argElim (const TypeNamespace) (const TermNamespace)
        argName = SystF.argElim id id
{- ORMOLU_ENABLE -}

-- | Version of removeExcessiveDestArgs that works on all the terms
removeExcessiveDestArgs' :: (LanguageBuiltins lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
removeExcessiveDestArgs' defs =
  PrtUnorderedDefs $
    flip runReader defs $
      M.fromList <$> mapM (secondM (defTermMapM removeExcessiveDestArgs)) (M.toList $ prtUODecls defs)

-- * Auxiliar Definitions

data Stages a b where
  Id :: Stages a a
  Comp :: String -> (a -> b) -> (String -> b -> IO ()) -> Stages b c -> Stages a c

runStages :: (MonadIO m) => Maybe [String] -> Stages a b -> a -> m b
runStages _dump Id a = return a
runStages dump (Comp stageName f dbg rest) a = do
  let b = f a
  when shouldDebug $ liftIO $ dbg stageName b
  runStages dump rest b
  where
    shouldDebug =
      case dump of
        Nothing -> False
        Just [] -> True
        Just prefs -> any (`L.isPrefixOf` stageName) prefs
