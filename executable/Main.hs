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
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.FromPlutusIR
import Pirouette.Term.Transformations
import Pirouette.Term.ConstraintTree
import Pirouette.Term.ToTla
import Pirouette.PlutusIR.Utils

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
import           Control.Arrow (second, (***))
import           Data.Data
import           Data.Functor
import           Data.Foldable (asum)
import qualified Data.List          as L
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
  , pullDestr     :: Maybe Int
  , expandExcl    :: Maybe [String]
  , withArguments :: [String]
  , exprWrapper   :: String
  , skeleton      :: Maybe FilePath
  } deriving Show

data Stage = ToTerm | ToTLA | ToCTree
  deriving Show

optsToCTreeOpts :: CliOpts -> CTreeOpts
optsToCTreeOpts co = CTreeOpts
  { coPruneMaybe = True
  , coWithArguments = withArguments co
  }

optsToTlaOpts :: (MonadIO m , MonadPirouette m) => CliOpts -> m TlaOpts
optsToTlaOpts co = do
  skel0 <- maybe (return defaultSkel) (liftIO . readFile) $ skeleton co
  skel  <- mkTLASpecWrapper skel0
  wr    <- mkTLAExprWrapper (exprWrapper co)
  return $ TlaOpts
    { toSymbExecOpts = optsToCTreeOpts co
    , toActionWrapper = wr
    , toSkeleton = skel
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
  pirouette file opts $ do
    flushLogs $ logInfo ("Running with opts: " ++ show opts)
    mainOpts cliOpts

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
mainOpts :: forall m . (MonadIO m) => CliOpts -> PrtT m ()
mainOpts opts = do
  sortedNames <- processDecls opts
  allDecls <- gets decls
  let relDecls =
        M.toList $ M.filterWithKey (\k _ -> contains (funNamePrefix opts) k) allDecls
  case stage opts of
    ToTerm  -> mapM_ (uncurry printDef) relDecls
    ToCTree -> mapM_ (uncurry printCTree) relDecls
    ToTLA   -> do
      when (length relDecls /= 1) $
        throwError' (PEOther "I need a single term to extract to TLA. Try a stricter --prefix")
      case head relDecls of
        (n, DFunction _ t _) -> toTla sortedNames n t
        (n, _)               -> throwError' (PEOther $ show n ++ " is not a function")
 where
    printDef name def = do
      let pdef = pretty def
      putStrLn' $ show $ vsep [pretty name <+> ":=", indent 2 pdef]
      putStrLn' ""

    printCTree name (DFunction _ def _) = do
      ct <- termToCTree (optsToCTreeOpts opts) name def
      putStrLn' $ show $ vsep [pretty name <+> ":=", indent 2 (pretty ct)]
      putStrLn' ""
    printCTree name _ = throwError' $ PEOther (show name ++ " is not a function")

    toTla :: [[Name]] -> Name -> PrtTerm -> PrtT m ()
    toTla sortedNames n t = do
      opts' <- optsToTlaOpts opts
      spec <- termToSpec opts' sortedNames n t
      putStrLn' (TLA.prettyPrintAS spec)

-- |Processes all declarations according to some transformations.
-- It outputs the list of names in an order compatible with dependencies.
-- Meaning that if `n0` and `n1` are in the same list, they are mutually dependent,
-- and if `n0` is in a list which is before the one which contains `n1`,
-- then `n0` does not depend of `n1` (`n1` might depend of `n0` or not).
processDecls :: (MonadIO m) => CliOpts -> PrtT m [[Name]]
processDecls opts = do
  ds  <- gets decls
  let allNames = M.keys ds
  sortedNames <- sortDeps allNames
  (remainingNames, dsPruned, _) <- foldM go ([], ds, []) sortedNames
  ds' <- mapM (defTermMapM transfo) dsPruned
  modify (\st -> st{decls = ds'})
  return $ reverse remainingNames
  where
    -- `transfo` contains the transformations applied to every term.
    transfo :: MonadPirouette m => PrtTerm -> m PrtTerm
    transfo =  constrDestrId
           >=> removeExcessiveDestArgs
           >=> cfoldmapSpecialize

    prefix = funNamePrefix opts

    -- This function makes sure to define the dependencies of a type/term F
    -- before defining F itself.
    -- To do so, it computes equivalence classes for the pre-order "depends of".
    -- The output list is a linearization of the order between classes,
    -- so if a class `A` is smaller than `B`
    -- (in the sense that elements of `B` depends of `A`)
    -- then `A` is guaranted to appear before `B`.
    -- The order of independent classes is unspecified.
    sortDeps :: (MonadPirouette m) => [Name] -> m [[Name]]
    sortDeps [] = return []
    sortDeps (d:ds) = do
      depsD <- S.map (R.argElim id id) <$> depsOf d
      let (couldBeBefore, after) = L.partition (`S.member` depsD) ds
      annotatedCouldBeBefore <-
        mapM (\x -> (x,) . S.member d . S.map (R.argElim id id) <$> depsOf x) couldBeBefore
      let (equiv, before) =
            bimap (map fst) (map fst) $ L.partition snd annotatedCouldBeBefore
      fmap (++) (sortDeps before) <*> (((d : equiv) :) <$> sortDeps after)

    go :: (MonadIO m)
       => ([[Name]], Decls Name P.DefaultFun, [(Name, PrtTerm)]) -> [Name]
       -> PrtT m ([[Name]], Decls Name P.DefaultFun, [(Name, PrtTerm)])
    -- An empty dependency class should not exist.
    go (names, decls, transfo) []  = undefined
    go (names, decls, transfo) [k] =
      if contains prefix k
      then do
          -- If the declaration is the one we are focused on,
          -- we do not want to suppress it, and apply some additional transformations.
          declRelevant <- transfoPrefix decls k
          decls' <- expandDefsIn transfo declRelevant k
          return ([k] : names, decls', transfo)
      else do
        decls' <- expandDefsIn transfo decls k
        case M.lookup k decls' of
          -- Any name should be declared.
          Nothing -> undefined
          Just (DFunction _ t _) ->
            if S.member (R.Arg k) (termNames t)
            -- If the function is recursive, we keep it in the declarations
            then return ([k] : names, decls', transfo)
            -- Otherwise, we delete it and store its definition,
            -- to inline it in the definitions relying on it.
            else
              return (names, M.delete k decls', (k, t) : transfo)
          _ -> return ([k] : names, decls', transfo)
    -- If the function is mutually recursive, we follow the same logic,
    -- but now, we have to inline a function in definition we have already dealt with.
    -- It is the purpose of the `expanseClass` function.
    go (names, decls, transfo) l = do
      (remNames, decls', newTransfo) <- expanseClass decls [] [] l
      finalDecls <- foldM (expandDefsIn transfo) decls' remNames
      return (remNames : names, finalDecls, newTransfo ++ transfo)

    expanseClass :: (MonadIO m)
                 => Decls Name P.DefaultFun -> [(Name, PrtTerm)] -> [Name] -> [Name]
                 -> PrtT m ([Name], Decls Name P.DefaultFun, [(Name, PrtTerm)])
    -- When all the name have been treated, the function terminates.
    expanseClass decls transfo acc []       = return (acc, decls, transfo)
    expanseClass decls transfo acc (k : ks) =
      -- The treatment of the function we are focused on is the same as in `go`.
      if contains prefix k
      then do
        declRelevant <- transfoPrefix decls k
        expanseClass declRelevant transfo (k : acc) ks
      else
        case M.lookup k decls of
          Nothing -> undefined
          Just (DFunction _ t _) ->
            if S.member (R.Arg k) (termNames t)
            -- If the function is recursive, we keep it in the declarations
            -- and put it in the accumulator, to be sure to expanse in it,
            -- if any other member of the equivalence class can be inlined.
            then expanseClass decls transfo (k : acc) ks
            -- Otherwise, we delete it, inline it in all the definitions of the dependency class,
            -- and store its definition, to expand the definitions relying on it, in the next classes.
            else do
              let decls' = M.delete k decls
              unfoldedDecls <- foldM (expandDefsIn [(k,t)]) decls' (acc ++ ks)
              expanseClass unfoldedDecls ((k, t) : transfo) acc ks
          _ -> expanseClass decls transfo (k : acc) ks

    -- `transfoPrefix` contains the transformations applied only to the function we are focused on.
    transfoPrefix :: (MonadIO m)
                  => Decls Name P.DefaultFun -> Name
                  -> PrtT m (Decls Name P.DefaultFun)
    transfoPrefix decls k =
      flushLogs $ do
        logDebug ("Processing " ++ show k)
        d' <-
          case M.lookup k decls of
            Just (DFunction r t ty) ->
              flip (DFunction r) ty <$> relevantTransfo t
            Just def                ->
              return def
            Nothing                 ->
              undefined
        return $ M.insert k d' decls

    relevantTransfo :: MonadPirouette m => PrtTerm -> m PrtTerm
    relevantTransfo =   destrNF
       >=> removeExcessiveDestArgs
       >=> maybe return pullNthDestr (pullDestr opts)

-- ** Auxiliar Defs

pirouette :: (MonadIO m) => FilePath -> PrtOpts -> PrtT m a -> m a
pirouette pir opts f =
  withParsedPIR pir $ \pirProg ->
  withDecls pirProg $ \toplvl decls0 -> do
    let decls = declsUniqueNames decls0
    let st = PrtState decls M.empty toplvl
    (eres, msgs) <- runPrtT opts st f
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
  return . either (Left . errorBundlePretty) (Right . Showable)
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
                       <*> parsePullDestr
                       <*> parseExpansionExcl
                       <*> parseWithArgs
                       <*> parseExprWrapper
                       <*> parseSkeletonFile

parseWithArgs :: Opt.Parser [String]
parseWithArgs = Opt.option (Opt.maybeReader (Just . r))
                     (  Opt.long "with-args"
                     <> Opt.short 'a'
                     <> Opt.value []
                     <> Opt.metavar "STR[,STR]*"
                     <> Opt.help "Renames the transition function arguments to the specified list")
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
                 <> Opt.metavar "TLA Expression"
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


parsePullDestr :: Opt.Parser (Maybe Int)
parsePullDestr = Opt.option (Just <$> Opt.auto)
                     (  Opt.long "pull-destr"
                     <> Opt.short 'p'
                     <> Opt.value Nothing
                     <> Opt.help "Bring the n-th destructor to the root if possible. Passing a zero does nothing, the constructor at the root is already at the root.")


parseExpansionExcl :: Opt.Parser (Maybe [String])
parseExpansionExcl = Opt.option (Just <$> Opt.maybeReader (Just . r))
                     (  Opt.long "expand-excl"
                     <> Opt.short 'e'
                     <> Opt.value Nothing
                     <> Opt.help "Expand all terms except those whose name contains a prefix of the values given in a comma-separated list as an argument")
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
