{-# LANGUAGE TemplateHaskell #-}
module Language.Pirouette.Example.QuasiQuoter (prog, term, ty) where

import Language.Pirouette.Example.Syntax
import Language.Pirouette.Example.ToTerm
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Text.Megaparsec
import Control.Monad.Except (runExcept)
import qualified Data.Map as M

prog :: QuasiQuoter
prog = quoter $ \str -> do
  p0 <- parseQ parseProgram str
  p1 <- trQ (uncurry trProgram p0)
  [e| p1 |]

term :: QuasiQuoter
term = quoter $ \str -> do
  p0 <- parseQ parseTerm str
  p1 <- trQ (trTerm [] [] p0)
  [e| p1 |]

ty :: QuasiQuoter
ty = quoter $ \str -> do
  p0 <- parseQ parseType str
  p1 <- trQ (trType [] p0)
  [e| p1 |]

-- * Internals

parseQ :: Parser a -> String -> Q a
parseQ p str = case parse p "<template-haskell>" str of
  Left err -> fail (errorBundlePretty err)
  Right r -> return r

trQ :: TrM a -> Q a
trQ f = case runExcept f of
  Left err -> fail err
  Right r -> return r

instance (Lift k, Lift v) => Lift (M.Map k v) where
  liftTyped m = unsafeTExpCoerce [e| M.fromList $(lift (M.toList m)) |]

quoter :: (String -> Q Exp) -> QuasiQuoter
quoter quote = QuasiQuoter
  { quoteExp  = quote
  , quotePat  = \_ -> failure0 "patterns"
  , quoteType = \_ -> failure0 "types"
  , quoteDec  = \_ -> failure0 "declarations"
  }
 where
  failure0 kind =
    fail ("this quasiquoter does not support splicing " ++ kind)
