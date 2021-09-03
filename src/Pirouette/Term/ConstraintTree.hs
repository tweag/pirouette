{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Pirouette.Term.ConstraintTree where

import           Pirouette.Monad
import           Pirouette.Monad.Maybe
import           Pirouette.Monad.Logger
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax
import           Pirouette.Term.FromPlutusIR
import           Pirouette.Term.Transformations
import           Pirouette.PlutusIR.Utils

import qualified PlutusCore as P (DefaultFun)

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Except
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.String
import           Data.List (foldl', elemIndex)
import           Data.Text.Prettyprint.Doc hiding (Pretty(..))

-- * Constraint Trees
--
-- $constraintrees
--
-- |A /constraint tree/ is a tree where each path corresponds to one execution path of
-- a closed WHNF term @t@. Say @t@ is, for example, @\x y z -> M@, the /constraint tree/
-- that is obtained through @execute' t@ should run @M@ treating @x, y@ and @z@ as symbols.
-- When the execution branches we issue a 'Choose' and everytime we learn about a new
-- constraint we issue a 'Constraint'. If the execution is finished, the 'Constraint'
-- carries a @Nothing@ in its second argument.
--
-- For example, say we call 'execute'' on the following term:
--
-- > (λst λi. [d/Input
-- >       i#0
-- >       (λm. [d/Counter [d/State st#2 (λds λds. ds#1)]
-- >           (λn. [d/Bool [b/ifThenElse [b/greaterThanEqualsInteger m#1 n#0]
-- >                                      c/True/Bool
-- >                                      c/False/Bool]
-- >                        (λthunk. M1)
-- >                        (λthunk. M2)
-- >                        c/Unit/Unit])
-- >       ])
-- >       (λm. [d/Counter [d/State st#2 (λds λds. ds#1)]
-- >           (λn. [c/Just/Maybe M3])
-- >       ])
-- > ])
--
-- The constraint tree we would obtain from symbolically executing it should be something like:
--
-- > Choose
-- >   [ (Match i#0 with Dec m)
-- >     :&: Choose [ Match [d/State st#2 (λds λds. ds#1)] with Counter n
-- >              :&: Choose [ Fact "b/greaterThanEqualsInteger m n"   :&: Result "M1"
-- >                         , Fact "! b/greaterThanEqualsInteber m n" :&: Result "M2"
-- >                         ]
-- >                ]
-- >  , (Match i#0 with Inc m)
-- >     :&: Choose [ Match [d/State st#2 (λds λds. ds#1)] wih Counter n
-- >              :&: Result "Just M3"
-- >                ]
-- >  ]

data CTreeOpts = CTreeOpts
  { coPruneMaybe    :: Bool
  , coWithArguments :: [String]
  }

type CTreeTerm name = Term name P.DefaultFun

data CTree name
  = Choose [CTree name]
  | (Constraint name) :&: (CTree name)
  | Result (CTreeTerm name)
  deriving (Eq, Show)

data Constraint name
  = Match (CTreeTerm name) (Type name) name [(name, Type name)]
  | Fact  Bool (CTreeTerm name)
  deriving (Eq, Show)

ctreeFirstMatches :: CTree name -> [name]
ctreeFirstMatches (Choose t) = concatMap ctreeFirstMatches t
ctreeFirstMatches (Match _ _ x _ :&: _) = [x]
ctreeFirstMatches _ = []

instance (Pretty name) => Pretty (Constraint name) where
  pretty (Match t ty c vs) = "Match" <+> pretty t <+> "with"
                               <+> pretty ty <> dot <> pretty c
                               <> parens (hsep . punctuate "," $ map pretty vs)
  pretty (Fact neg t)      = "Fact" <+> (if neg then ("~" <+>) . parens else id) (pretty t)

instance (Pretty name) => Pretty (CTree name) where
  pretty (Choose l)   = vsep ("Choose":map (indent 2 . pretty) l)
  pretty (cst :&: tr) = vsep [pretty cst <+> ":&:", indent 2 (pretty tr)]
  pretty (Result tr)  = "Result" <+> pretty tr

-- |Symbolicaly execute's a term into a /constraint tree/. Assumes that
-- the term in question is of the form @\ a b ... zz -> case i of ... @,
-- or, in words, its a closed WHNF abstraction whose body starts by pattern
-- matching on whatever value is supposed to be the user's input.
execute :: forall m . (MonadPirouette m) => PrtTerm -> m (CTree Name)
execute (R.App (R.F (nameIsITE -> True)) [R.Arg x, R.Arg t, R.Arg f])
  = Choose <$> sequence [ (Fact False x :&:) <$> execute t
                        , (Fact True  x :&:) <$> execute f
                        ]
execute t = do
  mdest <- runMaybeT $ unDest t
  case mdest of
    Nothing -> return (Result t)
    Just (dName, tyName, tyArgs, x, tyRet, cases) -> do
      cons <- constructors <$> typeDefOf tyName
      when (length cons /= length cases) $ throwError' (PEOther $ "Different number of cases for " ++ show dName)
      let ty = R.TyApp (R.F $ TyFree tyName) tyArgs
      Choose <$> zipWithM (constructMatching x ty) cases cons
     where
      constructMatching :: PrtTerm -> PrtType -> PrtTerm -> (Name, PrtType)
                        -> m (CTree Name)
      constructMatching v ty t (conName, conTy) =
        -- do
        -- isBool <- typeIsBool ty
        -- if isBool
        -- then (\ isFalse -> (Fact isFalse v :&:)) <$> consIsBoolVal False conName <*> execute t
        -- else
        let arity      = R.tyArity conTy
            (args, tl) = R.getNHeadLams arity t
        in (Match v ty conName args :&:) <$> execute tl

-- |Prune all the paths leading to @Result t@ such that @f t == Nothing@
pruneMaybe :: forall m . (MonadPirouette m)
           => CTree Name
           -> MaybeT m (CTree Name)
pruneMaybe (c :&: t)   = (c :&:) <$> pruneMaybe t
pruneMaybe (Result t)  = Result <$> MaybeT (go t)
  where go :: CTreeTerm Name -> m (Maybe (CTreeTerm Name))
        go t@(R.App (R.F (FreeName n)) args) = do
          mTerm <- runMaybeT $ consIsMaybeVal n
          return $ case mTerm of
            Nothing        -> Just t
            Just (Just _)  -> Just $ head (mapMaybe R.fromArg args)
            Just Nothing   -> Nothing
        go t = return (Just t)
pruneMaybe (Choose ts) = lift (mapMaybeM pruneMaybe ts) >>= choose
  where choose [] = fail "empty tree"
        choose ts = return (Choose ts)

termToCTree :: (MonadPirouette m) => CTreeOpts -> Name -> PrtDef -> m (CTree Name)
termToCTree opts name def =
  case def of
    DFunction _ t ty ->
      let argLength = length (coWithArguments opts) in
      let index = elemIndex "INPUT" (coWithArguments opts) in
      let tyOut = snd (R.tyFunArgs ty) in
      case elemIndex "INPUT" (coWithArguments opts) of
        Nothing -> throwError' $ PEOther "No argument declared as input"
        Just index ->
          let tyInput = fst (R.tyFunArgs ty) !! index in
          case nameOf tyInput of
            Nothing -> throwError' $ PEOther "The input is not a pattern-matchable type"
            Just tyName -> do
              dest <- blindDest tyOut <$> typeDefOf tyName
              let transiAbsInput = R.Lam (R.Ann $ fromString "DUMMY_INPUT") tyInput $
                    R.appN t (zipWith transitionArgs (coWithArguments opts) [argLength, argLength - 1 .. 1])
              let body = R.appN dest
                    [ R.Arg $ R.termPure (R.B (fromString "INPUT") (toInteger   (argLength - 1 - index)))
                    , R.Arg transiAbsInput
                    ]
              cleanBody <- constrDestrId body
              mctree <-
                execute cleanBody >>= runMaybeT . if coPruneMaybe opts then pruneMaybe else return
              logDebug $ "Translating Constraint Tree for " ++ show name
              case mctree of
                Nothing -> throwError' $ PEOther "termToCTree: empty tree"
                Just tr -> return tr
    _ -> throwError' $ PEOther (show name ++ " is not a function")

  where
    nameOf :: PrtType -> Maybe Name
    nameOf (R.TyApp (R.B (R.Ann x) _) []) =
      Just x
    nameOf (R.TyApp (R.F (TyFree x)) []) =
      Just x
    nameOf _ = Nothing

    blindDest :: PrtType -> PrtTypeDef -> PrtTerm
    blindDest tyOut (Datatype _ _ dest cons) =
      R.Lam (R.Ann $ fromString "i") (error "Fictive type of i") $ -- Since the generated term will be applied to two arguments,
        R.Lam (R.Ann $ fromString "f") (error "Fictive type of f") $ -- those 2 types should never be accessed.
          R.App (R.F (FreeName dest)) $
            R.Arg (R.termPure (R.B (fromString "i") 1)) :
            R.TyArg tyOut :
              map (R.Arg . consCase) cons

    consCase :: (Name, PrtType) -> PrtTerm
    consCase (n, ty) =
      let (argsTy,_) = R.tyFunArgs ty in
      createNLams "x" argsTy $
        R.App
          (R.B (fromString "f") (toInteger (length argsTy)))
          [R.Arg $ R.App (R.F (FreeName n)) (geneXs (length argsTy))]

    createNLams :: String -> [PrtType] -> PrtTerm -> PrtTerm
    createNLams s tys =
      let go [] _ = id
          go (h:tl) i =
            R.Lam (R.Ann $ fromString (s ++ show i)) h . go tl (i + 1)
      in
      go tys 0

    geneXs :: Int -> [R.Arg ty PrtTerm]
    geneXs n = go 0
      where
        go i =
          if i >= n
          then []
          else
            R.Arg
              (R.termPure
                (R.B (R.Ann $ fromString ("x" ++ show i)) (toInteger (n - 1 - i))))
            : go (i + 1)

    transitionArgs :: String -> Int -> R.Arg ty PrtTerm
    transitionArgs "INPUT" _ = R.Arg $ R.termPure (R.B (fromString "DUMMY_INPUT") 0)
    transitionArgs s       n = R.Arg $ R.termPure (R.B (fromString s) (toInteger n))
