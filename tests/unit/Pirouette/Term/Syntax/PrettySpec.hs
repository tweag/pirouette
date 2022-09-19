{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

module Pirouette.Term.Syntax.PrettySpec where

import Control.Monad.Reader (runReader)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Pirouette.Example (Ex, prog)
import Language.Pirouette.QuasiQuoter.Syntax (DataDecl, FunDecl, parseProgram)
import Pirouette.Monad (PrtUnorderedDefs (..))
import Pirouette.Term.Syntax.Pretty
import qualified Test.Tasty as Test
import qualified Test.Tasty.HUnit as Test
import Text.Megaparsec (runParserT)
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as L

example1 :: PrtUnorderedDefs Ex
example1 =
  [prog|
    data Either a b = Left : a -> Either a b | Right : b -> Either a b
    data Maybe a = Nothing : Maybe a | Just : a -> Maybe a
  |]

showProgram :: PrtUnorderedDefs Ex -> String
showProgram = renderSingleLineStr . pretty . Map.assocs . prtUODecls

readProgram :: String -> Either String (Map String (Either (DataDecl Ex) (FunDecl Ex)))
readProgram str =
  case runReader (P.runParserT (parseProgram @Ex) "program" str) Nothing of
    Left err -> Left (P.errorBundlePretty err)
    Right r -> Right r

assertRight :: Either String (Map String (Either (DataDecl Ex) (FunDecl Ex))) -> Test.Assertion
assertRight (Left err) = Test.assertFailure err
assertRight (Right _) = return ()

tests :: [Test.TestTree]
tests =
  [ Test.testCase
      "Pretty-printed program is parsable"
      (assertRight (readProgram . showProgram $ example1))
  ]
