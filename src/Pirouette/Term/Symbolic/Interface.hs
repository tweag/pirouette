{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}

module Pirouette.Term.Symbolic.Interface where

import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Symbolic.Eval
import qualified Pirouette.SMT as SMT
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Data.Aeson
import GHC.Generics
import Data.String
import Data.Void
import Data.Maybe
import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Monad
import Control.Monad.Except
import qualified Text.Megaparsec.Char.Lexer as L
import Pirouette.Term.Syntax.Pretty ( Pretty(pretty) )
import Control.Monad.Reader
import Pirouette.Term.Builtins (BuiltinTypes)

type Parser = Parsec Void String

data AnnotVar = AnnotVar {
  name :: String,
  typ :: String
}
  deriving (Generic, Show)
instance FromJSON AnnotVar

newtype NativeCond = NativeCond {native :: String}
  deriving (Generic, Show)
instance FromJSON NativeCond

data Condition =
    And {and :: [Condition]}
  | Or {or :: [NativeCond]}
  | Native NativeCond
  | ASTCond {cond :: String}
  deriving (Generic, Show)
instance FromJSON Condition

data OutputCond = OutputCond {
  resultName :: String,
  conditionBody :: Condition
}
  deriving (Generic, Show)
instance FromJSON OutputCond

data SMTLevelDef = SMTLevelDef {
  fun :: String,
  args :: [AnnotVar],
  resultType :: String,
  definition :: String
}
  deriving (Generic, Show)
instance FromJSON SMTLevelDef

newtype UniversalProp = UniversalProp {
  forall :: UniversalContent
}
  deriving (Generic, Show)
instance FromJSON UniversalProp

data UniversalContent = UniversalContent {
  vars :: [AnnotVar],
  prop :: String
}
  deriving (Generic, Show)
instance FromJSON UniversalContent

data ConstraintDescription = ConstraintDescription {
  inputs :: [AnnotVar],
  outputCond :: OutputCond,
  inputCond :: Condition,
  additionalDefs :: [SMTLevelDef],
  axioms :: [UniversalProp]
}
  deriving (Generic, Show)
instance FromJSON ConstraintDescription

data UserDeclaredConstraints lang = UserDeclaredConstraints {
  udcInputs :: [(Name, Type lang)],
  udcOutputCond :: OutCond lang,
  udcInputCond :: InCond lang,
  udcAdditionalDefs :: IO [SimpleSMT.SExpr],
  udcAxioms :: IO ()
}

parseConstraintDescription :: (Read (BuiltinTypes lang)) => (SimpleSMT.Solver, SimpleSMT.Solver) -> ConstraintDescription -> UserDeclaredConstraints  lang
parseConstraintDescription
  solvers@(_, solver_good_at_unsat)
  ConstraintDescription{..} =
  let udcInputs = map parseAnnotVar inputs
      !udcOutputCond = parseOutputCond outputCond
      !udcInputCond = parseInputCond inputCond
      udcAdditionalDefs = mapM (parseAdditionalDefs solvers) additionalDefs
      udcAxioms = mapM_ (parseAxioms solver_good_at_unsat) axioms
  in
  UserDeclaredConstraints {..}

parseAnnotVar :: (Read (BuiltinTypes lang)) => AnnotVar -> (Name, Type  lang )
parseAnnotVar AnnotVar{..} =
  (fromString name, parseType typ)

parseOutputCond :: (Read (BuiltinTypes lang)) => OutputCond -> OutCond  lang
parseOutputCond OutputCond{..} =
  OutCond $ parseCondAsFunction resultName conditionBody

parseInputCond :: (Read (BuiltinTypes lang)) => Condition -> InCond  lang
parseInputCond cond = InCond $ parseCond cond

parseAdditionalDefs :: (SimpleSMT.Solver, SimpleSMT.Solver) -> SMTLevelDef -> IO SimpleSMT.SExpr
parseAdditionalDefs (s1, s2) SMTLevelDef{..} = do
  void $ SimpleSMT.defineFunRec
    s1
    fun
    (map parseAnnotVarAsSMT args)
    (parseSExpr resultType)
    (parseSMTFun definition)
  SimpleSMT.defineFunRec
    s2
    fun
    (map parseAnnotVarAsSMT args)
    (parseSExpr resultType)
    (parseSMTFun definition)

parseAxioms :: SimpleSMT.Solver -> UniversalProp -> IO ()
parseAxioms solver (UniversalProp UniversalContent{..}) =
  SimpleSMT.assert solver $
    SimpleSMT.forall
      (map parseAnnotVarAsSMT vars)
      (parseSExpr prop)


parseType :: (Read (BuiltinTypes lang)) => String -> Type lang
parseType s = fromJust $ parseMaybe parseType' s

parseType' :: (Read (BuiltinTypes lang)) => Parser (Type lang)
parseType' =
  try parseTyApp <|>
  try parseBuiltin <|>
  parseElementaryType

  where
    parseTyApp :: (Read (BuiltinTypes lang)) => Parser (Type lang)
    parseTyApp = do
      void $ string "TyApp "
      hd <- parseElementaryType
      void $ char ' '
      args <- parseList parseType'
      return $ SystF.appN hd args

    parseBuiltin :: (Read (BuiltinTypes lang)) => Parser (Type lang)
    parseBuiltin = do
      void $ string "TyBuiltin "
      builtin <- read <$> some (alphaNumChar <|> char '_')
      return $ SystF.TyApp (SystF.Free (TyBuiltin builtin)) []

    parseElementaryType :: Parser (Type lang)
    parseElementaryType = do
      name <- fromString <$> some (alphaNumChar <|> char '_')
      return $ tyVar name

      where
        tyVar name = SystF.TyApp (SystF.Free (TySig name)) []

parseCond :: (Read (BuiltinTypes lang)) => Condition -> Constraint  lang
parseCond c = parseCondAsFunction "" c undefined

parseCondAsFunction :: (Read (BuiltinTypes lang)) => String -> Condition -> TermMeta  lang  SymVar -> Constraint  lang
parseCondAsFunction var (And conds) t =
  foldMap (\c -> parseCondAsFunction var c t) conds
parseCondAsFunction _ (Or conds) _ =
  SMT.And [SMT.Native (SimpleSMT.orMany $ map (parseSExpr . native) conds)]
parseCondAsFunction _ (Native c) _ =
  SMT.And [SMT.Native $ (parseSExpr . native) c]
parseCondAsFunction var (ASTCond c) t =
  SMT.And [parseAtomicCondAsFunction var c t]

parseSMTFun :: String -> SimpleSMT.SExpr -> SimpleSMT.SExpr
parseSMTFun s =
  fromJust $ parseMaybe parseSMTFun' s

parseSMTFun' :: Parser (SimpleSMT.SExpr -> SimpleSMT.SExpr)
parseSMTFun' = do
  void $ char '\\'
  var <- some (alphaNumChar <|> char '_')
  void $ string " -> "
  parseSExprAsFun var

parseParenSExprAsFun :: String -> Parser (SimpleSMT.SExpr -> SimpleSMT.SExpr)
parseParenSExprAsFun var =
  try (theVar var) <|>
  try (betweenParen $ parseMatch var) <|>
  try (betweenParen $ parseApp var) <|>
  try (betweenParen $ parseSmtOp2 var) <|>
  try (betweenParen (const <$> parseSymbol)) <|>
  try (const <$> parseNativeType) <|>
  betweenParen (const <$> parseInt)

parseSExprAsFun :: String -> Parser (SimpleSMT.SExpr -> SimpleSMT.SExpr)
parseSExprAsFun var =
  try (theVar var) <|>
  try (parseMatch var) <|>
  try (parseApp var) <|>
  try (parseSmtOp2 var) <|>
  try (const <$> parseSymbol) <|>
  try (const <$> parseNativeType) <|>
  (const <$> parseInt)

theVar :: String -> Parser (a -> a)
theVar var = do
  guard (var /= "")
  void $ string var
  return id

parseMatch :: String -> Parser (SimpleSMT.SExpr -> SimpleSMT.SExpr)
parseMatch var = do
  void $ string "match "
  t <- parseParenSExprAsFun var
  void $ char ' '
  l <- parseListAsFun (parsePairAsFun (parseSExprAsFun var) (parseSExprAsFun var))
  return $ SimpleSMT.match <$> t <*> l

parseSmtOp2 :: String -> Parser (SimpleSMT.SExpr -> SimpleSMT.SExpr)
parseSmtOp2 var = do
  op <- parseSExprOp2
  e1 <- parseParenSExprAsFun var
  void $ char ' '
  e2 <- parseParenSExprAsFun var
  return $ asOp op <$> e1 <*> e2

parseApp :: String -> Parser (SimpleSMT.SExpr -> SimpleSMT.SExpr)
parseApp var = do
  void $ string "app "
  e1 <- parseParenSExprAsFun var
  void $ char ' '
  e2 <- parseListAsFun (parseSExprAsFun var)
  return $ SimpleSMT.app <$> e1 <*> e2

parseSymbol :: Parser SimpleSMT.SExpr
parseSymbol = do
  void $ string "symbol \""
  name <- some (alphaNumChar <|> char '_')
  void $ char '\"'
  return $ SimpleSMT.symbol name

parseNativeType :: Parser SimpleSMT.SExpr
parseNativeType =
  choice [
    SimpleSMT.tInt <$ string "tInt",
    SimpleSMT.tBool <$ string "tBool"
  ]

parseInt :: Parser SimpleSMT.SExpr
parseInt = do
  void $ string "int "
  SimpleSMT.int <$> L.decimal

parseSExpr :: String -> SimpleSMT.SExpr
parseSExpr s = fromJust $ parseMaybe parseSExpr' s

parseSExpr' :: Parser SimpleSMT.SExpr
parseSExpr' =
  parseSExprAsFun "" <*> return undefined

data SExprOp2 =
    SExprEq
  | SExprAdd
  | SExprLt
  | SExprGe

asOp :: SExprOp2 -> SimpleSMT.SExpr -> SimpleSMT.SExpr -> SimpleSMT.SExpr
asOp SExprEq t u = SimpleSMT.eq t u
asOp SExprAdd t u = SimpleSMT.add t u
asOp SExprLt t u = SimpleSMT.lt t u
asOp SExprGe t u = SimpleSMT.geq t u

parseSExprOp2 :: Parser SExprOp2
parseSExprOp2 =
  choice [
    SExprEq <$ string "eq ",
    SExprAdd <$ string "add ",
    SExprLt <$ string "lt ",
    SExprGe <$ string "ge "
  ]

parseAtomicCondAsFunction :: (Read (BuiltinTypes lang)) => String -> String -> TermMeta  lang  SymVar -> SMT.AtomicConstraint  lang  SymVar
parseAtomicCondAsFunction var cond =
  fromJust $ parseMaybe (parseAtomicCondAsFunction' var) cond

parseAtomicCondAsFunction' :: (Read (BuiltinTypes lang)) => String -> Parser (TermMeta  lang  SymVar -> SMT.AtomicConstraint  lang  SymVar)
parseAtomicCondAsFunction' var =
  try parseAssign <|>
  try (const <$> parseVarEq) <|>
  parseTermEq

  where
    parseAssign :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> SMT.AtomicConstraint  lang  SymVar)
    parseAssign = do
      void $ string "Assign "
      varAssigned <- some (alphaNumChar <|> char '_')
      void $ char ' '
      t <- parseParenTermAsFun
      return $ SMT.Assign (fromString varAssigned) <$> t

    parseVarEq :: Parser (SMT.AtomicConstraint  lang  SymVar)
    parseVarEq = do
      void $ string "VarEq "
      varA <- some (alphaNumChar <|> char '_')
      void $ char ' '
      varB <- some (alphaNumChar <|> char '_')
      return $ SMT.VarEq (fromString varA) (fromString varB)

    parseTermEq :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> SMT.AtomicConstraint  lang  SymVar)
    parseTermEq = do
      void $ string "TermEq "
      t <- parseParenTermAsFun
      void $ char ' '
      u <- parseParenTermAsFun
      return $ SMT.NonInlinableSymbolEq <$> t <*> u

    parseParenTermAsFun :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> TermMeta  lang  SymVar)
    parseParenTermAsFun =
      try (theVar var) <|>
      try (betweenParen app) <|>
      betweenParen lam

    parseTermAsFun :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> TermMeta  lang  SymVar)
    parseTermAsFun =
      try (theVar var) <|>
      try app <|>
      lam

    app :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> TermMeta  lang  SymVar)
    app = do
      void $ string "App "
      varApplied <- betweenParen parseVarMeta
      void $ string " ["
      args <- parseArgListAsFun
      void $ char ']'
      return $ SystF.App varApplied <$> args

      where

        parseArgListAsFun :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> [ArgMeta  lang  SymVar])
        parseArgListAsFun = do
          mRes <- optional (try nonEmpty)
          return $ fromMaybe (const []) mRes

          where

            nonEmpty :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> [ArgMeta  lang  SymVar])
            nonEmpty = do
              hd <- parseTermAsFun
              mTail <-
                optional . try $ do
                  void $ char ','
                  nonEmpty
              case mTail of
                Nothing -> return $ \t -> [SystF.TermArg (hd t)]
                Just l -> return $ \t -> SystF.TermArg (hd t) : l t

    lam :: (Read (BuiltinTypes lang)) => Parser (TermMeta  lang  SymVar -> TermMeta  lang  SymVar)
    lam = do
      void $ string "Lam \""
      varName <- some (alphaNumChar <|> char '_')
      void $ string "\" "
      ty <- parseType'
      void $ char ' '
      body <- parseParenTermAsFun
      return $ SystF.Lam (fromString varName) (typeToMeta ty) <$> body

parseVarMeta :: Parser (VarMeta  lang  SymVar)
parseVarMeta = do
  try free <|> bound

  where
    -- One cannot have language polymorphic buitins,
    -- so we assume that we are only dealing with constants.
    free :: Parser (VarMeta  lang  SymVar)
    free = do
      void $ string "Free \""
      fVar <- some (alphaNumChar <|> char '_')
      void $ char '\"'
      return $ SystF.Free (TermSig $ fromString fVar)

    bound :: Parser (VarMeta  lang  SymVar)
    bound = do
      void $ string "Bound \""
      name <- some (alphaNumChar <|> char '_')
      void $ string "\" "
      SystF.Bound (fromString name) <$> L.decimal

parseAnnotVarAsSMT :: AnnotVar -> (String, SimpleSMT.SExpr)
parseAnnotVarAsSMT AnnotVar{..} =
  (name, parseSExpr typ)

betweenParen :: Parser a -> Parser a
betweenParen p = do
  void $ char '('
  a <- p
  void $ char ')'
  return a

parseListAsFun :: Parser (a -> b) -> Parser (a -> [b])
parseListAsFun p = do
  void $ char '['
  mRes <- optional (try nonEmpty)
  void $ char ']'
  return $ fromMaybe (const []) mRes

  where

    nonEmpty = do
      hd <- p
      mTail <-
        optional . try $ do
          void $ string ", "
          nonEmpty
      case mTail of
        Nothing -> return $ \t -> [hd t]
        Just l -> return $ \t -> hd t : l t

parseList :: Parser a -> Parser [a]
parseList p = do
  void $ char '['
  mRes <- optional (try nonEmpty)
  void $ char ']'
  return $ fromMaybe [] mRes

  where

    nonEmpty = do
      hd <- p
      mTail <-
        optional . try $ do
          void $ string ", "
          nonEmpty
      case mTail of
        Nothing -> return [hd]
        Just l -> return $ hd : l

parsePairAsFun :: Parser (a -> b) -> Parser (a -> c) -> Parser (a -> (b, c))
parsePairAsFun p q = do
  void $ char '('
  resA <- p
  void $ string ", "
  resB <- q
  void $ char ')'
  return $ \t -> (resA t, resB t)

runIncorrectness :: (SymEvalConstr  lang  m, MonadIO m, Read (BuiltinTypes lang)) => FilePath -> Term  lang  -> m ()
runIncorrectness fil t = do
  paths <- symevalT $ do
    solvers <- SymEvalT $ lift $ SMT.SolverT ask
    constrDescription <- liftIO $ eitherDecodeFileStrict fil
    case constrDescription of
      Left l -> error $ "Impossible to parse this file\n" ++ l
      Right cstDescr -> do
        let !UserDeclaredConstraints {..} = parseConstraintDescription solvers cstDescr
        void $ liftIO udcAdditionalDefs
        liftIO udcAxioms
        svars <- declSymVars udcInputs
        let tApplied = SystF.appN (termToMeta t) $ map (SystF.TermArg . (`SystF.App` []) . SystF.Meta) svars
        liftIO $ putStrLn $ "Conditionally evaluating: " ++ show (pretty tApplied)
        conditionalEval tApplied udcOutputCond udcInputCond
  if null paths
  then liftIO $ putStrLn "Condition VERIFIED"
  else mapM_ (liftIO . print . pretty) paths
