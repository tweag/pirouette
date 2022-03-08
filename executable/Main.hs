{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Main where

-- , termToCTree)

import Control.Arrow (first, second, (***))
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer.Strict
import Data.Bifunctor (bimap)
import qualified Data.ByteString as BS
import Data.Data
import Data.Foldable (asum)
import Data.Functor
import Data.List (groupBy, isSuffixOf, partition)
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (isJust)
import Data.Semigroup ((<>))
import qualified Data.Set as S
import Data.String
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Debug.Trace (trace)
import Development.GitRev
import qualified Flat
import Flat.Decoder.Types
import GHC.IO.Encoding
import qualified Language.TLAPlus.Pretty as TLA
import qualified Language.TLAPlus.Syntax as TLA
import Options.Applicative ((<**>))
import qualified Options.Applicative as Opt
import Pirouette.Monad
import Pirouette.Monad.Logger
import Pirouette.Monad.Maybe
import Pirouette.PlutusIR.SMT
import Pirouette.PlutusIR.ToTerm
import Pirouette.PlutusIR.Utils
import Pirouette.Specializer.Rewriting
import Pirouette.Term.ConstraintTree (CTreeOpts (..))
import Pirouette.Term.Defunctionalize
import Pirouette.Term.Symbolic.Eval as SymbolicEval
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.ToTla
import Pirouette.Term.Transformations
import Pirouette.Transformations
import qualified Pirouette.Transformations.Defunctionalization as SFD
import Pirouette.Transformations.Monomorphization
import qualified PlutusCore as P
import qualified PlutusCore.Flat as P
import qualified PlutusCore.Pretty as P
import PlutusIR.Core.Type (Program)
import qualified PlutusIR.Parser as PIR
import Prettyprinter hiding (Pretty (..))
import System.Environment (getArgs)
import System.Exit
import Text.Megaparsec (ParseErrorBundle)
import Text.Megaparsec.Error (errorBundlePretty)

---------------------

-- * CLI Options * --

---------------------

data CliOpts = CliOpts
  { stage :: Stage,
    funNamePrefix :: String,
    asFunction :: Bool,
    withArguments :: [String],
    exprWrapper :: String,
    skeleton :: Maybe FilePath,
    pruneMaybe :: Bool,
    dontDefun :: Bool,
    tySpecializer :: [String],
    checkSanity :: Bool,
    noInlining :: Bool
  }
  deriving (Show)

data Stage = ToTerm | ToTLA | ToCTree | SymbolicExecution
  deriving (Show)

optsToCTreeOpts :: CliOpts -> CTreeOpts
optsToCTreeOpts co =
  CTreeOpts
    { coPruneMaybe = not (pruneMaybe co),
      coWithArguments = withArguments co
    }

optsToTlaOpts :: (MonadIO m, PirouetteReadDefs PlutusIR m) => CliOpts -> m TlaOpts
optsToTlaOpts co = do
  skel0 <- maybe (return defaultSkel) (liftIO . readFile) $ skeleton co
  skel <- if asFunction co then return mkEmptySpecWrapper else mkTLASpecWrapper skel0
  wr <- mkTLAExprWrapper (exprWrapper co)
  let spz = mkTLATySpecializer (tySpecializer co)
  return $
    TlaOpts
      { toSymbExecOpts = optsToCTreeOpts co,
        toActionWrapper = wr,
        toSkeleton = skel,
        toSpecialize = spz,
        defsPostproc = if dontDefun co then id else defunctionalize,
        toAsFunction = asFunction co
      }
  where
    defaultSkel =
      unlines
        [ "---- MODULE " ++ funNamePrefix co ++ "----",
          "EXTENDS Plutus",
          "----",
          "----",
          "===="
        ]

-----------------------

-- * Main Function * --

-----------------------

main :: IO ()
main = do
  setLocaleEncoding utf8
  Opt.execParser pirouetteOpts >>= \(cliOpts, file, opts) ->
    pirouette file opts $ \uDefs -> do
      flushLogs $ logInfo ("Running with opts: " ++ show opts)
      mainOpts cliOpts uDefs

-- ** Return Codes and Command definitions

ecInternalError :: ExitCode
ecInternalError = ExitFailure 1

ecParseError :: ExitCode
ecParseError = ExitFailure 12

ecTranslationError :: ExitCode
ecTranslationError = ExitFailure 13

ecNoAvailableParser :: ExitCode
ecNoAvailableParser = ExitFailure 14

ecProcessDeclsFailed :: ExitCode
ecProcessDeclsFailed = ExitFailure 15

ecTooManyDefs :: ExitCode
ecTooManyDefs = ExitFailure 16

-- | Converts a PIR file to a term, displaying the results to the user.
--  The 'CliOpts' argument controls which transformations should be applied,
--  which definitions the user is interested into, etc...
mainOpts :: forall m. (MonadIO m) => CliOpts -> PrtUnorderedDefs PlutusIR -> PrtT m ()
mainOpts opts uDefs = do
  decls <- processDecls opts uDefs
  flip runReaderT decls $ do
    allDecls <- prtAllDefs
    let relDecls =
          M.toList $ M.filterWithKey (\k _ -> startsBy (funNamePrefix opts) k) allDecls
    mainTerm <- prtMain
    let relDecls' =
          if asFunction opts
            then
              let mainFunName =
                    fromString $
                      if funNamePrefix opts == ""
                        then "DEFAULT_FUN_NAME"
                        else funNamePrefix opts
                  mainDef =
                        DFunction NonRec mainTerm $ R.TyApp (R.F $ TyFree (fromString "Bool")) []
               in (mainFunName, mainDef) : relDecls
            else relDecls
    case stage opts of
      SymbolicExecution -> do
        when (length relDecls' /= 1) $
          throwError' (PEOther "I need a single term to symbolically execute. Try a stricter --prefix")
        uncurry symbExec (head relDecls')
      ToTerm -> mapM_ (uncurry printDef) relDecls'
      ToCTree -> mapM_ (uncurry printCTree) relDecls'
      ToTLA -> do
        when (length relDecls' /= 1) $
          throwError' (PEOther "I need a single term to extract to TLA. Try a stricter --prefix")
        uncurry toTla (head relDecls')
  where
    printDef name def = do
      let pdef = pretty def
      putStrLn' $ show $ vsep [pretty name <+> ":=", indent 2 pdef]
      putStrLn' ""

    printCTree name def = do
      error "printCTree: constraint tree will be replaced; this is a WIP"
    -- ct <- termToCTree (optsToCTreeOpts opts) name def
    -- putStrLn' $ show $ vsep [pretty name <+> ":=", indent 2 (pretty ct)]
    -- putStrLn' ""

    toTla n t = do
      opts' <- optsToTlaOpts opts
      spec <- termToSpec opts' n t
      putStrLn' (TLA.prettyPrintAS spec)

    symbExec n (DFunction _ t _) = SymbolicEval.runFor n t

processDecls :: (LanguageDef lang, PrettyLang lang, MonadIO m) => CliOpts -> PrtUnorderedDefs lang -> PrtT m (PrtOrderedDefs lang)
processDecls opts uDefs = do
  -- If the user wishes, we can perform checks on the sanity of the translation
  -- from PlutusIR to PrtDefs
  when (checkSanity opts) $ do
    runReaderT checkDeBruijnIndices uDefs

  -- Otherwise, we proceed normally
  noMutDefs <- elimEvenOddMutRec $ SFD.defunctionalize $ monomorphize uDefs
  let oDefs =
        if noInlining opts
          then noMutDefs
          else expandAllNonRec (startsBy (funNamePrefix opts)) noMutDefs
  postDs <- runReaderT (sequence $ M.map processOne $ prtDecls oDefs) oDefs
  return $ oDefs {prtDecls = postDs}
  where
    generalTransformations ::
      (PirouetteReadDefs lang m) =>
      PrtTerm lang ->
      m (PrtTerm lang)
    generalTransformations =
      constrDestrId
        -- >=> applyRewRules
        >=> removeExcessiveDestArgs

    processOne = defTermMapM generalTransformations

-- ** Auxiliar Defs

pirouette ::
  (MonadIO m) =>
  FilePath ->
  PrtOpts ->
  (PrtUnorderedDefs PlutusIR -> PrtT m a) ->
  m a
pirouette pir opts f =
  withParsedPIR pir $ \pirProg ->
    withDecls pirProg $ \toplvl0 decls0 -> do
      let (decls, toplvl) = declsUniqueNames decls0 toplvl0
      let defs = PrtUnorderedDefs decls toplvl
      (eres, msgs) <- runPrtT opts (f defs)
      mapM_ printLogMessage msgs
      case eres of
        Left err -> liftIO $ print err >> exitWith ecInternalError
        Right res -> return res

withDecls ::
  (MonadIO m, Show l) =>
  Program P.TyName P.Name P.DefaultUni P.DefaultFun l ->
  (PrtTerm PlutusIR -> Decls PlutusIR Name -> m a) ->
  m a
withDecls pir cont = do
  case runExcept $ trProgram pir of
    Left err -> putStrLn' (show err) >> liftIO (exitWith ecTranslationError)
    Right (t, decls) -> cont t decls

putStrLn' :: (MonadIO m) => String -> m ()
putStrLn' = liftIO . putStrLn

-- | Opens and parses a file containint a 'Program' then passes it to a subsequent function.
--  Because we want to homogeneously handle results from the binary deserializer or the parser,
--  and these produce a program with @()@ and 'PIR.SrcLoc' respectively, we require the function
--  to be parametric on the types of labels
withParsedPIR ::
  (MonadIO m) =>
  FilePath ->
  (forall l. Show l => Program P.TyName P.Name P.DefaultUni P.DefaultFun l -> m a) ->
  m a
withParsedPIR fileName f = do
  res <-
    if
        | ".pir" `isSuffixOf` fileName -> openAndParsePIR fileName
        | ".flat" `isSuffixOf` fileName -> openAndDecodeFlat fileName
        | otherwise -> liftIO (exitWith ecNoAvailableParser)
  case res of
    Left err -> putStrLn' err >> liftIO (exitWith ecParseError)
    Right (Showable pir) -> f pir

-- Simple existential wrapper for the Programs coming from 'openAndDecodeFlat' and 'openAndParsePIR'
data Showable (f :: * -> *) :: * where
  Showable :: (Show x) => f x -> Showable f

openAndDecodeFlat ::
  (MonadIO m) =>
  FilePath ->
  m (Either String (Showable (Program P.TyName P.Name P.DefaultUni P.DefaultFun)))
openAndDecodeFlat fileName = do
  content <- liftIO $ BS.readFile fileName
  return . either (Left . show) (Right . Showable) $
    pirDecoder content
  where
    pirDecoder :: BS.ByteString -> Flat.Decoded (Program P.TyName P.Name P.DefaultUni P.DefaultFun ())
    pirDecoder = Flat.unflat

openAndParsePIR ::
  (MonadIO m) =>
  FilePath ->
  m (Either String (Showable (Program P.TyName P.Name P.DefaultUni P.DefaultFun)))
openAndParsePIR fileName = do
  content <- liftIO $ T.readFile fileName
  return . either (Left . show) (Right . Showable) $
    PIR.parse (PIR.program @P.DefaultUni @P.DefaultFun) fileName content

startsBy :: String -> Name -> Bool
startsBy str n = T.pack str `T.isPrefixOf` nameString n

----------------------

-- * CLI Parsers  * --

----------------------

pirouetteOpts :: Opt.ParserInfo (CliOpts, FilePath, PrtOpts)
pirouetteOpts =
  Opt.info
    ( (,,) <$> parseCliOpts
        <*> parseArgument
        <*> parseOptions
        <**> Opt.helper
        <**> versionOpts
    )
    $ Opt.fullDesc
      <> Opt.header vERSIONSTR
      <> Opt.footer "Run pirouette COMMAND --help for more help on specific commands"
      <> Opt.progDesc pd
  where
    pd =
      unwords
        [ "Runs pirouette with the specified command.",
          "The program exists with 0 for success and non-zero for failure."
        ]

parseCliOpts :: Opt.Parser CliOpts
parseCliOpts =
  CliOpts <$> parseStage
    <*> parsePrefix
    <*> parseAsFunction
    <*> parseWithArgs
    <*> parseExprWrapper
    <*> parseSkeletonFile
    <*> parsePruneMaybe
    <*> parseDontDefunctionalize
    <*> parseTySpecializer
    <*> parseTrSanity
    <*> parseNoInlining

parseTrSanity :: Opt.Parser Bool
parseTrSanity =
  Opt.switch
    ( Opt.long "sanity-check"
        <> Opt.help "Perform a series of extra checks, can help with debugging"
    )

parseNoInlining :: Opt.Parser Bool
parseNoInlining =
  Opt.switch
    ( Opt.long "no-inlining"
        <> Opt.help "Disable inlining of definitions when generating TLA+ programs"
    )

parseWithArgs :: Opt.Parser [String]
parseWithArgs =
  Opt.option
    (Opt.maybeReader (Just . r))
    ( Opt.long "with-args"
        <> Opt.short 'a'
        <> Opt.value []
        <> Opt.metavar "STR[,STR]*"
        <> Opt.help "Renames the transition function arguments to the specified list. The argument INPUT is considered as the user input one and is used to define actions."
    )
  where
    r :: String -> [String]
    r = filter (/= ",") . groupBy (\x y -> ',' `notElem` [x, y]) . filter (/= ' ')

parseSkeletonFile :: Opt.Parser (Maybe FilePath)
parseSkeletonFile =
  Opt.option
    (fmap Just Opt.str)
    ( Opt.metavar "FILE"
        <> Opt.long "tla-skel"
        <> Opt.short 's'
        <> Opt.value Nothing
        <> Opt.help "Uses the given module as a skeleton. The produced definitions will be inserted after the first TLA.AS_Separator found. A separator is a line consisting of at least four '-'"
    )

parseExprWrapper :: Opt.Parser String
parseExprWrapper =
  Opt.option
    Opt.str
    ( Opt.long "action-wrapper"
        <> Opt.short 'w'
        <> Opt.value "st' = ___"
        <> Opt.metavar "TLAExpression"
        <> Opt.help "How to wrap the produced actions into action-formulas"
    )

parseStage :: Opt.Parser Stage
parseStage = termOnly Opt.<|> treeOnly Opt.<|> symbExec Opt.<|> pure ToTLA

termOnly :: Opt.Parser Stage
termOnly =
  Opt.flag'
    ToTerm
    ( Opt.long "term-only"
        <> Opt.help "By default we try to produce a TLA module from the given PIR file. If --term-only is given, we display the terms that have been produced before symbolically evaluating and translating to TLA"
    )

treeOnly :: Opt.Parser Stage
treeOnly =
  Opt.flag'
    ToCTree
    ( Opt.long "tree-only"
        <> Opt.help "By default we try to produce a TLA module from the given PIR file. If --tree-only is given, we display the terms that have been produced before symbolically evaluating and translating to TLA"
    )

symbExec :: Opt.Parser Stage
symbExec =
  Opt.flag'
    SymbolicExecution
    ( Opt.long "symb-exec"
        <> Opt.help "By default we try to produce a TLA module from the given PIR file. If --symb-exec is given, we display the terms that have been produced by symbolically evaluating the top-level one"
    )

parsePrefix :: Opt.Parser String
parsePrefix =
  Opt.option
    Opt.str
    ( Opt.long "prefix"
        <> Opt.value ""
        <> Opt.help "Extract only the terms whose name contains the specified prefix"
    )

parseAsFunction :: Opt.Parser Bool
parseAsFunction =
  Opt.switch
    ( Opt.long "as-function"
        <> Opt.help "Directly generate a TLA+ function. Do not transform it into an action."
    )

parsePruneMaybe :: Opt.Parser Bool
parsePruneMaybe =
  Opt.switch
    ( Opt.long "dont-prune-maybe"
        <> Opt.help "Do not suppress the maybe type in the output of the transition function."
    )

parseDontDefunctionalize :: Opt.Parser Bool
parseDontDefunctionalize =
  Opt.switch
    ( Opt.long "dont-defunctionalize"
        <> Opt.help "Do not defunctionalize functions passed as constructor arguments."
    )

parseTySpecializer :: Opt.Parser [String]
parseTySpecializer =
  Opt.option
    (Opt.maybeReader (Just . r))
    ( Opt.long "ty-spz"
        <> Opt.value []
        <> Opt.help "Declare the types to be specialized, ALL to specialize all types."
    )
  where
    r :: String -> [String]
    r = filter (/= ",") . groupBy (\x y -> ',' `notElem` [x, y]) . filter (/= ' ')

parseArgument :: Opt.Parser FilePath
parseArgument = Opt.argument Opt.str (Opt.metavar "FILE")

parseOptions :: Opt.Parser PrtOpts
parseOptions =
  PrtOpts <$> parseLogLevel
    <*> parseLogFocus

parseLogFocus :: Opt.Parser [String]
parseLogFocus =
  Opt.option
    (Opt.maybeReader (Just . r))
    ( Opt.long "log-focus"
        <> Opt.value []
        <> Opt.metavar "STR[,STR]*"
        <> Opt.help "Only logs messages whose context contains one of the comma separated strings."
    )
  where
    r :: String -> [String]
    r = filter (/= ",") . groupBy (\x y -> ',' `notElem` [x, y]) . filter (/= ' ')

parseLogLevel :: Opt.Parser LogLevel
parseLogLevel =
  asum
    [ Opt.flag'
        WARN
        ( Opt.long "quiet"
            <> Opt.short 'q'
            <> Opt.help "Runs on quiet mode; almost no information out"
        ),
      Opt.flag'
        DEBUG
        ( Opt.long "debug"
            <> Opt.short 'g'
            <> Opt.help "Runs with a more output than normal"
        ),
      Opt.flag'
        TRACE
        ( Opt.long "trace"
            <> Opt.help "Prints tracing messages mode"
        ),
      pure INFO
    ]

vERSIONSTR :: String
vERSIONSTR = "pirouette [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]"

versionOpts :: Opt.Parser (a -> a)
versionOpts = Opt.infoOption vERSIONSTR (Opt.long "version")
