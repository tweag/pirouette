{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.ByteString as BS
import Data.Foldable (asum)
import Data.List (groupBy, isSuffixOf)
import qualified Data.Map as M
import Data.String
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Development.GitRev
import qualified Flat
import GHC.IO.Encoding
import Options.Applicative ((<**>))
import qualified Options.Applicative as Opt
import Pirouette.Monad
import Pirouette.Monad.Logger
import Language.Pirouette.PlutusIR.SMT ()
import Language.Pirouette.PlutusIR.Builtins
import Language.Pirouette.PlutusIR.ToTerm
import Pirouette.Term.Builtins
import Pirouette.Term.Symbolic.Eval as SymbolicEval
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.Transformations
import Pirouette.Transformations
import qualified Pirouette.Transformations.Defunctionalization as SFD
import Pirouette.Transformations.Monomorphization
import qualified PlutusCore as P
import qualified PlutusIR.Core.Type as PIR (Program)
import qualified PlutusIR.Parser as PIR
import Prettyprinter hiding (Pretty (..))
import System.Exit

---------------------

-- * CLI Options * --

---------------------

data CliOpts = CliOpts
  { stage :: Stage,
    funNamePrefix :: String,
    asFunction :: Bool,
    checkSanity :: Bool,
    noInlining :: Bool
  }
  deriving (Show)

data Stage = ToTerm | SymbolicExecution
  deriving (Show)

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
mainOpts :: forall m. (MonadIO m) => CliOpts -> PrtUnorderedDefs BuiltinsOfPIR -> PrtT m ()
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
                        DFunction NonRec mainTerm $ R.TyApp (R.Free $ TySig (fromString "Bool")) []
               in (mainFunName, mainDef) : relDecls
            else relDecls
    case stage opts of
      SymbolicExecution -> do
        when (length relDecls' /= 1) $
          throwError' (PEOther "I need a single term to symbolically execute. Try a stricter --prefix")
        uncurry symbolicExec (head relDecls')
      ToTerm -> mapM_ (uncurry printDef) relDecls'
  where
    printDef name def = do
      let pdef = pretty def
      putStrLn' $ show $ vsep [pretty name <+> ":=", indent 2 pdef]
      putStrLn' ""

    symbolicExec n (DFunction _ t _) = SymbolicEval.runFor n t
    symbolicExec _ _ = throwError' (PEOther "Impossible to symbolic execute a symbol which is not a function")

processDecls :: (LanguageBuiltins lang, PrettyLang lang, MonadIO m) => CliOpts -> PrtUnorderedDefs lang -> PrtT m (PrtOrderedDefs lang)
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
      Term lang ->
      m (Term lang)
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
  (PrtUnorderedDefs BuiltinsOfPIR -> PrtT m a) ->
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
  PIR.Program P.TyName P.Name P.DefaultUni P.DefaultFun l ->
  (Term BuiltinsOfPIR -> Decls BuiltinsOfPIR -> m a) ->
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
  (forall l. Show l => PIR.Program P.TyName P.Name P.DefaultUni P.DefaultFun l -> m a) ->
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
  m (Either String (Showable (PIR.Program P.TyName P.Name P.DefaultUni P.DefaultFun)))
openAndDecodeFlat fileName = do
  content <- liftIO $ BS.readFile fileName
  return . either (Left . show) (Right . Showable) $
    pirDecoder content
  where
    pirDecoder :: BS.ByteString -> Flat.Decoded (PIR.Program P.TyName P.Name P.DefaultUni P.DefaultFun ())
    pirDecoder = Flat.unflat

openAndParsePIR ::
  (MonadIO m) =>
  FilePath ->
  m (Either String (Showable (PIR.Program P.TyName P.Name P.DefaultUni P.DefaultFun)))
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

parseStage :: Opt.Parser Stage
parseStage = termOnly Opt.<|> symbExec

termOnly :: Opt.Parser Stage
termOnly =
  Opt.flag'
    ToTerm
    ( Opt.long "term-only"
        <> Opt.help "By default we try to produce a TLA module from the given PIR file. If --term-only is given, we display the terms that have been produced before symbolically evaluating and translating to TLA"
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
