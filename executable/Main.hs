{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE MultiWayIf           #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}

module Main where

import Pirouette.Monad
import Pirouette.Monad.Maybe
import Pirouette.Monad.Logger
import Pirouette.Transformations
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.FromPlutusIR
import Pirouette.Term.Transformations
import Pirouette.Term.ConstraintTree (CTreeOpts(..), termToCTree)
import Pirouette.Term.ToTla
import Pirouette.PlutusIR.Utils
import Pirouette.Specializer.Rewriting

import qualified PlutusIR.Parser    as PIR
import qualified PlutusCore         as P
import qualified PlutusCore.Flat    as P
import qualified PlutusCore.Pretty  as P
import           PlutusIR.Core.Type (Program)

import qualified Language.TLAPlus.Pretty as TLA
import qualified Language.TLAPlus.Syntax as TLA

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer.Strict
import           Control.Arrow (first, second, (***))
import           Data.Data
import           Data.Functor
import           Data.Foldable (asum)
import qualified Data.List          as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map           as M
import           Data.Maybe            (isJust)
import qualified Data.Text          as T
import qualified Data.Text.IO       as T
import qualified Data.Set as S
import           Data.List (isSuffixOf, groupBy, partition)
import qualified Data.ByteString    as BS
import           Data.Semigroup ((<>))
import           Data.Bifunctor (bimap)
import           Development.GitRev
import qualified Flat
import           Flat.Decoder.Types
import           Options.Applicative ((<**>))
import qualified Options.Applicative as Opt
import           System.Environment (getArgs)
import           System.Exit
import           Text.Megaparsec       (ParseErrorBundle)
import           Text.Megaparsec.Error (errorBundlePretty)

import           Data.Text.Prettyprint.Doc hiding (Pretty(..))

---------------------
-- * CLI Options * --
---------------------

data CliOpts = CliOpts
  { stage         :: Stage
  , funNamePrefix :: String
  , withArguments :: [String]
  , exprWrapper   :: String
  , skeleton      :: Maybe FilePath
  , pruneMaybe    :: Bool
  , tySpecializer :: [String]
  } deriving Show

data Stage = ToTerm | ToTLA | ToCTree
  deriving Show

optsToCTreeOpts :: CliOpts -> CTreeOpts
optsToCTreeOpts co = CTreeOpts
  { coPruneMaybe = not (pruneMaybe co)
  , coWithArguments = withArguments co
  }

optsToTlaOpts :: (MonadIO m , PirouetteReadDefs m) => CliOpts -> m TlaOpts
optsToTlaOpts co = do
  skel0  <- maybe (return defaultSkel) (liftIO . readFile) $ skeleton co
  skel   <- mkTLASpecWrapper skel0
  wr     <- mkTLAExprWrapper (exprWrapper co)
  let spz = mkTLATySpecializer (tySpecializer co)
  return $ TlaOpts
    { toSymbExecOpts = optsToCTreeOpts co
    , toActionWrapper = wr
    , toSkeleton = skel
    , toSpecialize = spz
    }
  where
    defaultSkel = unlines
      ["---- MODULE " ++ funNamePrefix co ++ "----"
      ,"EXTENDS Plutus"
      ,"----"
      ,"----"
      ,"===="
      ]

-----------------------
-- * Main Function * --
-----------------------

main :: IO ()
main = Opt.execParser pirouetteOpts >>= \(cliOpts, file, opts) ->
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

-- |Converts a PIR file to a term, displaying the results to the user.
-- The 'CliOpts' argument controls which transformations should be applied,
-- which definitions the user is interested into, etc...
mainOpts :: forall m . (MonadIO m) => CliOpts -> PrtUnorderedDefs -> PrtT m ()
mainOpts opts uDefs = do
  decls <- processDecls opts uDefs
  flip runReaderT decls $ do
    allDecls <- prtAllDefs
    let relDecls =
          M.toList $ M.filterWithKey (\k _ -> contains (funNamePrefix opts) k) allDecls
    case stage opts of
      ToTerm  -> mapM_ (uncurry printDef) relDecls
      ToCTree -> mapM_ (uncurry printCTree) relDecls
      ToTLA   -> do
        when (length relDecls /= 1) $
          throwError' (PEOther "I need a single term to extract to TLA. Try a stricter --prefix")
        uncurry toTla (head relDecls)
  where
    printDef name def = do
      let pdef = pretty def
      putStrLn' $ show $ vsep [pretty name <+> ":=", indent 2 pdef]
      putStrLn' ""

    printCTree name def = do
      ct <- termToCTree (optsToCTreeOpts opts) name def
      putStrLn' $ show $ vsep [pretty name <+> ":=", indent 2 (pretty ct)]
      putStrLn' ""

    toTla n t = do
      opts' <- optsToTlaOpts opts
      spec <- termToSpec opts' n t
      putStrLn' (TLA.prettyPrintAS spec)


processDecls :: (MonadIO m) => CliOpts -> PrtUnorderedDefs -> PrtT m PrtOrderedDefs
processDecls opts uDefs = do
  oDefs  <- expandAllNonRec (contains (funNamePrefix opts)) <$> elimEvenOddMutRec uDefs
  mRules <- parseFileTransfo transfoFilePath
  postDs <- runReaderT (sequence $ M.map (processOne mRules) $ prtDecls oDefs) oDefs
  return $ oDefs { prtDecls = postDs }
 where
    generalTransformations :: (PirouetteReadDefs m)
                           => [RewritingRule PrtTerm PrtTerm] -> PrtTerm -> m PrtTerm
    generalTransformations mRules =
          constrDestrId
      >=> flip (foldM (flip applyTransfo)) mRules
      >=> removeExcessiveDestArgs

    processOne = defTermMapM . generalTransformations

-- ** Auxiliar Defs

pirouette :: (MonadIO m) => FilePath -> PrtOpts
          -> (PrtUnorderedDefs -> PrtT m a) -> m a
pirouette pir opts f =
  withParsedPIR pir $ \pirProg ->
  withDecls pirProg $ \toplvl decls0 -> do
    let decls = declsUniqueNames decls0
    let defs  = PrtUnorderedDefs decls toplvl
    (eres, msgs) <- runPrtT opts (f defs)
    mapM_ printLogMessage msgs
    case eres of
      Left  err -> liftIO $ print err >> exitWith ecInternalError
      Right res -> return res

withDecls :: (MonadIO m, Show l)
          => Program P.TyName P.Name P.DefaultUni P.DefaultFun l
          -> (PrtTerm -> Decls Name P.DefaultFun -> m a)
          -> m a
withDecls pir cont =
  case runExcept $ trProgram pir of
    Left err         -> putStrLn' (show err) >> liftIO (exitWith ecTranslationError)
    Right (t, decls) -> cont t decls

putStrLn' :: (MonadIO m) => String -> m ()
putStrLn' = liftIO . putStrLn

-- |Opens and parses a file containint a 'Program' then passes it to a subsequent function.
-- Because we want to homogeneously handle results from the binary deserializer or the parser,
-- and these produce a program with @()@ and 'PIR.SrcLoc' respectively, we require the function
-- to be parametric on the types of labels
withParsedPIR :: (MonadIO m)
              => FilePath
              -> (forall l . Show l => Program P.TyName P.Name P.DefaultUni P.DefaultFun l -> m a)
              -> m a
withParsedPIR fileName f = do
  res <- if| ".pir"  `isSuffixOf` fileName -> openAndParsePIR fileName
           | ".flat" `isSuffixOf` fileName -> openAndDecodeFlat fileName
           | otherwise                     -> liftIO (exitWith ecNoAvailableParser)
  case res of
    Left err             -> putStrLn' err >> liftIO (exitWith ecParseError)
    Right (Showable pir) -> f pir

-- Simple existential wrapper for the Programs coming from 'openAndDecodeFlat' and 'openAndParsePIR'
data Showable (f :: * -> *) :: * where
  Showable :: (Show x) => f x -> Showable f

openAndDecodeFlat :: (MonadIO m)
                  => FilePath
                  -> m (Either String (Showable (Program P.TyName P.Name P.DefaultUni P.DefaultFun)))
openAndDecodeFlat fileName = do
  content <- liftIO $ BS.readFile fileName
  return . either (Left . show) (Right . Showable)
         $ pirDecoder content
  where
    pirDecoder :: BS.ByteString -> Flat.Decoded (Program P.TyName P.Name P.DefaultUni P.DefaultFun ())
    pirDecoder = Flat.unflat

openAndParsePIR :: (MonadIO m)
                => FilePath
                -> m (Either String (Showable (Program P.TyName P.Name P.DefaultUni P.DefaultFun)))
openAndParsePIR fileName = do
  content <- liftIO $ T.readFile fileName
  return . either (Left . show) (Right . Showable)
         $ PIR.parse (PIR.program @P.DefaultUni @P.DefaultFun) fileName content

contains :: String -> Name -> Bool
contains str n = T.pack str `T.isPrefixOf` nameString n

----------------------
-- * CLI Parsers  * --
----------------------

pirouetteOpts :: Opt.ParserInfo (CliOpts, FilePath, PrtOpts)
pirouetteOpts = Opt.info ((,,) <$> parseCliOpts
                            <*> parseArgument
                            <*> parseOptions
                            <**> Opt.helper
                            <**> versionOpts)
           $ Opt.fullDesc
            <> Opt.header vERSIONSTR
            <> Opt.footer "Run pirouette COMMAND --help for more help on specific commands"
            <> Opt.progDesc pd
  where
    pd = unwords
           [ "Runs pirouette with the specified command."
           , "The program exists with 0 for success and non-zero for failure."
           ]

parseCliOpts :: Opt.Parser CliOpts
parseCliOpts = CliOpts <$> parseStage
                       <*> parsePrefix
                       <*> parseWithArgs
                       <*> parseExprWrapper
                       <*> parseSkeletonFile
                       <*> parsePruneMaybe
                       <*> parseTySpecializer

parseWithArgs :: Opt.Parser [String]
parseWithArgs = Opt.option (Opt.maybeReader (Just . r))
                     (  Opt.long "with-args"
                     <> Opt.short 'a'
                     <> Opt.value []
                     <> Opt.metavar "STR[,STR]*"
                     <> Opt.help "Renames the transition function arguments to the specified list. The argument INPUT is considered as the user input one and is used to define actions.")
  where
    r :: String -> [String]
    r = filter (/= ",") . groupBy (\x y -> ',' `notElem` [x,y]) . filter (/= ' ')

parseSkeletonFile :: Opt.Parser (Maybe FilePath)
parseSkeletonFile = Opt.option (fmap Just Opt.str)
                  (  Opt.metavar "FILE"
                  <> Opt.long "tla-skel"
                  <> Opt.short 's'
                  <> Opt.value Nothing
                  <> Opt.help "Uses the given module as a skeleton. The produced definitions will be inserted after the first TLA.AS_Separator found. A separator is a line consisting of at least four '-'")

parseExprWrapper :: Opt.Parser String
parseExprWrapper = Opt.option Opt.str
                 (  Opt.long "action-wrapper"
                 <> Opt.short 'w'
                 <> Opt.value "st' = ___"
                 <> Opt.metavar "TLAExpression"
                 <> Opt.help "How to wrap the produced actions into action-formulas")

parseStage :: Opt.Parser Stage
parseStage = termOnly Opt.<|> treeOnly Opt.<|> pure ToTLA

termOnly :: Opt.Parser Stage
termOnly = Opt.flag' ToTerm
           (Opt.long "term-only"
           <> Opt.help "By default we try to produce a TLA module from the given PIR file. If --term-only is given, we display the terms that have been produced before symbolically evaluating and translating to TLA"
           )

treeOnly :: Opt.Parser Stage
treeOnly = Opt.flag' ToCTree
           (Opt.long "tree-only"
           <> Opt.help "By default we try to produce a TLA module from the given PIR file. If --tree-only is given, we display the terms that have been produced before symbolically evaluating and translating to TLA"
           )

parsePrefix :: Opt.Parser String
parsePrefix = Opt.option Opt.str
             (  Opt.long "prefix"
             <> Opt.value ""
             <> Opt.help "Extract only the terms whose name contains the specified prefix")

parsePruneMaybe :: Opt.Parser Bool
parsePruneMaybe = Opt.switch
                  (  Opt.long "dont-prune-maybe"
                  <> Opt.help "Do not suppress the maybe type in the output of the transition function."
                  )

parseTySpecializer :: Opt.Parser [String]
parseTySpecializer = Opt.option (Opt.maybeReader (Just . r))
                     ( Opt.long "ty-spz"
                     <> Opt.value []
                     <> Opt.help "Declare the types to be specialized, ALL to specialize all types.")
  where
    r :: String -> [String]
    r = filter (/= ",") . groupBy (\x y -> ',' `notElem` [x,y]) . filter (/= ' ')

parseArgument :: Opt.Parser FilePath
parseArgument = Opt.argument Opt.str (Opt.metavar "FILE")

parseOptions :: Opt.Parser PrtOpts
parseOptions = PrtOpts <$> parseLogLevel
                          <*> parseLogFocus

parseLogFocus :: Opt.Parser [String]
parseLogFocus = Opt.option (Opt.maybeReader (Just . r))
                     (  Opt.long "log-focus"
                     <> Opt.value []
                     <> Opt.metavar "STR[,STR]*"
                     <> Opt.help "Only logs messages whose context contains one of the comma separated strings.")
  where
    r :: String -> [String]
    r = filter (/= ",") . groupBy (\x y -> ',' `notElem` [x,y]) . filter (/= ' ')

parseLogLevel :: Opt.Parser LogLevel
parseLogLevel = asum
  [ Opt.flag' WARN  ( Opt.long "quiet"
                   <> Opt.short 'q'
                   <> Opt.help "Runs on quiet mode; almost no information out"
                    )
  , Opt.flag' DEBUG ( Opt.long "debug"
                   <> Opt.short 'g'
                   <> Opt.help "Runs with a more output than normal"
                    )
  , Opt.flag' TRACE ( Opt.long "trace"
                   <> Opt.help "Prints tracing messages mode"
                    )
  , pure INFO
  ]

vERSIONSTR :: String
vERSIONSTR = "pirouette [" ++ $(gitBranch) ++ "@" ++ $(gitHash) ++ "]"

versionOpts :: Opt.Parser (a -> a)
versionOpts = Opt.infoOption vERSIONSTR (Opt.long "version")
