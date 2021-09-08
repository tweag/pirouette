{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

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

import           Control.Arrow ( second )
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
-- > Choose i#0 of type Input
-- >   [ Match with Dec m ->
-- >     Choose [d/State st#2 (λds λds. ds#1)] of type Counter
-- >       [ Match with Counter n ->
-- >         Choose "b/greaterThanEqualsInteger m n" of type Bool
-- >           [ Match with True -> Result "M1"
-- >           , Match with False -> Result "M2"
-- >           ]
-- >       ]
-- >   , Match with Inc m ->
-- >     Choose [d/State st#2 (λds λds. ds#1)] of type Counter
-- >       [ Match with Counter n -> Result "Just M3" ]
-- >   ]

data CTreeOpts = CTreeOpts
  { coPruneMaybe    :: Bool
  , coWithArguments :: [String]
  }

type CTreeTerm name = Term name P.DefaultFun

data CTree name
  = Choose (CTreeTerm name) (Type name) [(Constraint name, CTree name)]
  | Result (CTreeTerm name)
  deriving (Eq, Show)

data Constraint name
  = Match name [(name, Type name)]
  deriving (Eq, Show)

ctreeFirstMatches :: CTree name -> [name]
ctreeFirstMatches (Choose _ _ t) =
  map (constraintFirstMatches . fst) t
ctreeFirstMatches _ = []

constraintFirstMatches :: Constraint name -> name
constraintFirstMatches (Match x _) = x

instance (Pretty name) => Pretty (Constraint name) where
  pretty (Match c vs) =
    "Match with" <+> pretty c
      <> parens (hsep . punctuate "," $ map pretty vs)

instance (Pretty name) => Pretty (CTree name) where
  pretty (Choose t ty l) =
    vsep
      ( "Choose" <+> pretty t <+> "of type" <+> pretty ty
      : map (\(cst,tr) -> indent 2 $ vsep [pretty cst <+> "->", indent 2 (pretty tr)]) l
      )
  pretty (Result tr)     = "Result" <+> pretty tr

-- |Symbolicaly execute's a term into a /constraint tree/. Assumes that
-- the term in question is of the form @\ a b ... zz -> case i of ... @,
-- or, in words, its a closed WHNF abstraction whose body starts by pattern
-- matching on whatever value is supposed to be the user's input.
execute :: forall m . (MonadPirouette m) => PrtTerm -> m (CTree Name)
execute t = do
  mdest <- runMaybeT $ unDest t
  case mdest of
    Nothing -> return (Result t)
    Just (dName, tyName, tyArgs, x, tyRet, cases, excess) -> do
      unless (null excess) $ throwError' (PEOther "ConstraintTree.execute'ing a term with excessive destr args. Please use removeExcessiveDestrArgs before execute")
      cons <- constructors <$> typeDefOf tyName
      -- Since excessive arguments to a destructor are suppressed by the transformation
      -- `removeExcessiveDest`, this error should never be triggered.
      when (length cons /= length cases) $ throwError' (PEOther $ "Different number of cases for " ++ show dName)
      let ty = R.TyApp (R.F $ TyFree tyName) tyArgs
      Choose x ty <$> zipWithM constructMatching cases cons
     where
      constructMatching :: PrtTerm -> (Name, PrtType)
                        -> m (Constraint Name,CTree Name)
      constructMatching t (conName, conTy) =
        let arity      = R.tyArity conTy
            (args, tl) = R.getNHeadLams arity t
        in (Match conName args, ) <$> execute tl

-- |Prune all the paths leading to @Result t@ such that @f t == Nothing@
pruneMaybe :: forall m . (MonadPirouette m)
           => CTree Name
           -> MaybeT m (CTree Name)
pruneMaybe (Result t)  = Result <$> MaybeT (go t)
  where go :: CTreeTerm Name -> m (Maybe (CTreeTerm Name))
        go t@(R.App (R.F (FreeName n)) args) = do
          mTerm <- runMaybeT $ consIsMaybeVal n
          return $ case mTerm of
            Nothing        -> Just t
            Just (Just _)  -> Just $ head (mapMaybe R.fromArg args)
            Just Nothing   -> Nothing
        go t = return (Just t)
pruneMaybe (Choose x ty ts) =
  lift (mapMaybeM ((\(a,b) -> (a,) <$> b) . second pruneMaybe) ts) >>= choose
  where choose [] = fail "empty tree"
        choose ts = return (Choose x ty ts)

termToCTree :: (MonadPirouette m) => CTreeOpts -> Name -> PrtDef -> m (CTree Name)
termToCTree opts name def =
  case def of
    DFunction _ t ty -> do
      body <- chooseHeadCase t ty (coWithArguments opts) "INPUT"
      mctree <-
        execute body >>= runMaybeT . if coPruneMaybe opts then pruneMaybe else return
      logDebug $ "Translating Constraint Tree for " ++ show name
      case mctree of
        Nothing -> throwError' $ PEOther "termToCTree: empty tree"
        Just tr -> return tr
    _ -> throwError' $ PEOther (show name ++ " is not a function")
