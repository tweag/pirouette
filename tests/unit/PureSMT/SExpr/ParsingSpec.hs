{-# LANGUAGE QuasiQuotes #-}

module PureSMT.SExpr.ParsingSpec (tests) where

import Control.Monad (zipWithM_)
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.List (unfoldr)
import PureSMT.SExpr
import Test.Tasty
import Test.Tasty.HUnit
import Text.RawString.QQ

tests :: [TestTree]
tests = do
  example <- examples
  return $
    testCase (name example) $ do
      let expecteds = parse example
          gots = unfoldr readSExpr $ LBS.pack $ content example
      zipWithM_
        ( \expected got ->
            assertBool
              ("  parsed:   '" ++ show got ++ "\n  expected: '" ++ show expected)
              $ expected == got
        )
        expecteds
        gots
      let numExpected = length expecteds
          numGot = length gots
      assertBool
        ( "parsed "
            ++ show numGot
            ++ " expressions, expected "
            ++ show numExpected
        )
        $ numExpected == numGot

-- | A source is a list of SMTLib2 commands, available in several different formats
-- for testing purposes.
data Example = Example {name :: String, content :: String, parse :: [SExpr]}

-- | A list of examples SMT-Lib2 files. Most of them were taken from the official
-- SMT-Lib website:
-- https://smtlib.cs.uiowa.edu/examples.shtml
examples :: [Example]
examples =
  [ Example
      "assertions"
      [r|
      ; Getting assertions
      (set-option :produce-assertions true)
      (set-logic QF_UF)
      (declare-const p Bool) (declare-const q Bool)
      (push 1)
      (assert (or p q))
      (push 1)
      (assert (not q))
      (get-assertions)
      ; ((or p q)
      ;  (not q)
      ; )
      (pop 1)
      (get-assertions)
      ; ((or p q))
      (pop 1)
      (get-assertions)
      ; ()
      (exit)
      |]
      [ List [Atom "set-option", Atom ":produce-assertions", Atom "true"],
        List [Atom "set-logic", Atom "QF_UF"],
        List [Atom "declare-const", Atom "p", Atom "Bool"],
        List [Atom "declare-const", Atom "q", Atom "Bool"],
        List [Atom "push", Atom "1"],
        List [Atom "assert", List [Atom "or", Atom "p", Atom "q"]],
        List [Atom "push", Atom "1"],
        List [Atom "assert", List [Atom "not", Atom "q"]],
        List [Atom "get-assertions"],
        List [Atom "pop", Atom "1"],
        List [Atom "get-assertions"],
        List [Atom "pop", Atom "1"],
        List [Atom "get-assertions"],
        List [Atom "exit"]
      ],
    Example
      "assignments"
      [r|
      ; Getting assignments
      (set-option :produce-assignments true)
      (set-logic QF_UF)
      (declare-const p Bool) (declare-const q Bool) (declare-const r Bool)
      (assert (not (=(! (and (! p :named P) q) :named PQ) (! r :named R))))
      (check-sat)
      ; sat
      (get-assignment)
      ; ((P true) (R false) (PQ true))
      (exit)
      |]
      [ List [Atom "set-option", Atom ":produce-assignments", Atom "true"],
        List [Atom "set-logic", Atom "QF_UF"],
        List [Atom "declare-const", Atom "p", Atom "Bool"],
        List [Atom "declare-const", Atom "q", Atom "Bool"],
        List [Atom "declare-const", Atom "r", Atom "Bool"],
        List
          [ Atom "assert",
            List
              [ Atom "not",
                List
                  [ Atom "=",
                    List
                      [ Atom "!",
                        List
                          [ Atom "and",
                            List [Atom "!", Atom "p", Atom ":named", Atom "P"],
                            Atom "q"
                          ],
                        Atom ":named",
                        Atom "PQ"
                      ],
                    List [Atom "!", Atom "r", Atom ":named", Atom "R"]
                  ]
              ]
          ],
        List [Atom "check-sat"],
        List [Atom "get-assignment"],
        List [Atom "exit"]
      ],
    Example
      "boolean"
      [r|
      ; Basic Boolean example
      (set-logic QF_UF)
      (declare-const p Bool)
      (assert (and p (not p)))
      (check-sat) ; returns 'unsat'
      (exit)
      |]
      [ List [Atom "set-logic", Atom "QF_UF"],
        List [Atom "declare-const", Atom "p", Atom "Bool"],
        List
          [ Atom "assert",
            List [Atom "and", Atom "p", List [Atom "not", Atom "p"]]
          ],
        List [Atom "check-sat"],
        List [Atom "exit"]
      ],
    Example
      "info"
      [r|
      ; Getting info
      (get-info :name)
      ; (: name "CVC4")
      (get-info :version )
      ; (:version "4.0" )
      (get-info :authors )
      ; (:authors "The CVC4 Team" )
      (exit)
      |]
      [ List [Atom "get-info", Atom ":name"],
        List [Atom "get-info", Atom ":version"],
        List [Atom "get-info", Atom ":authors"],
        List [Atom "exit"]
      ],
    Example
      "integer arithmetic"
      [r|
      ; Integer arithmetic
      (set-logic QF_LIA)
      (declare-const x Int)
      (declare-const y Int)
      (assert (= (- x y) (+ x (- y) 1)))
      (check-sat)
      ; unsat
      (exit)
      |]
      [ List [Atom "set-logic", Atom "QF_LIA"],
        List [Atom "declare-const", Atom "x", Atom "Int"],
        List [Atom "declare-const", Atom "y", Atom "Int"],
        List
          [ Atom "assert",
            List
              [ Atom "=",
                List [Atom "-", Atom "x", Atom "y"],
                List [Atom "+", Atom "x", List [Atom "-", Atom "y"], Atom "1"]
              ]
          ],
        List [Atom "check-sat"],
        List [Atom "exit"]
      ],
    Example
      "modeling sequential code (SSA)"
      [r|
      ; Modeling sequential code in SSA form
      ;; Buggy swap
      ; int x, y;
      ; int t = x;
      ; x = y;
      ; y = x;

      (set-logic QF_UFLIA)
      (set-option :produce-models true)
      (declare-fun x (Int) Int)  (declare-fun y (Int) Int)
      (declare-fun t (Int) Int)
      (assert (= (t 0) (x 0)))
      (assert (= (y 1) (t 0)))
      (assert (= (x 1) (y 1)))

      (assert
          (not
              (and (= (x 1) (y 0)) (= (y 1) (x 0)))))
      (check-sat)
      (get-value ((x 0) (y 0) (x 1) (y 1)))
      ; possible returned valuation:
      ; (((x 0) (- 1)) ((y 0) 2) ((x 1) (- 1)) ((y 1) (- 1)))
      (get-model)
      ; possible returned model:
      ; (
      ;  (define-fun x ((_ufmt_1 Int)) Int (- 1))
      ;  (define-fun y ((_ufmt_1 Int)) Int (ite (= _ufmt_1 1) (- 1) 2))
      ;  (define-fun t ((_ufmt_1 Int)) Int (- 1))
      ; )
      (exit)
      |]
      [ List [Atom "set-logic", Atom "QF_UFLIA"],
        List [Atom "set-option", Atom ":produce-models", Atom "true"],
        List [Atom "declare-fun", Atom "x", List [Atom "Int"], Atom "Int"],
        List [Atom "declare-fun", Atom "y", List [Atom "Int"], Atom "Int"],
        List [Atom "declare-fun", Atom "t", List [Atom "Int"], Atom "Int"],
        List
          [ Atom "assert",
            List [Atom "=", List [Atom "t", Atom "0"], List [Atom "x", Atom "0"]]
          ],
        List
          [ Atom "assert",
            List [Atom "=", List [Atom "y", Atom "1"], List [Atom "t", Atom "0"]]
          ],
        List
          [ Atom "assert",
            List [Atom "=", List [Atom "x", Atom "1"], List [Atom "y", Atom "1"]]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "not",
                List
                  [ Atom "and",
                    List
                      [ Atom "=",
                        List [Atom "x", Atom "1"],
                        List [Atom "y", Atom "0"]
                      ],
                    List
                      [ Atom "=",
                        List [Atom "y", Atom "1"],
                        List [Atom "x", Atom "0"]
                      ]
                  ]
              ]
          ],
        List [Atom "check-sat"],
        List
          [ Atom "get-value",
            List
              [ List [Atom "x", Atom "0"],
                List [Atom "y", Atom "0"],
                List [Atom "x", Atom "1"],
                List [Atom "y", Atom "1"]
              ]
          ],
        List [Atom "get-model"],
        List [Atom "exit"]
      ],
    Example
      "modeling sequential code (bitvectors)"
      [r|
      ; Modeling sequential code with bitvectors
      ;; Correct swap with no temp var
      ; int x, y;
      ; x = x + y;
      ; y = x - y;
      ; x = x - y;

      (set-logic QF_BV)
      (set-option :produce-models true)

      (declare-const x_0 (_ BitVec 32))
      (declare-const x_1 (_ BitVec 32))
      (declare-const x_2 (_ BitVec 32))
      (declare-const y_0 (_ BitVec 32))
      (declare-const y_1 (_ BitVec 32))
      (assert (= x_1 (bvadd x_0 y_0)))
      (assert (= y_1 (bvsub x_1 y_0)))
      (assert (= x_2 (bvsub x_1 y_1)))

      (assert (not
          (and (= x_2 y_0)
              (= y_1 x_0))))
      (check-sat)
      ; unsat
      (exit)
      |]
      [ List [Atom "set-logic", Atom "QF_BV"],
        List [Atom "set-option", Atom ":produce-models", Atom "true"],
        List
          [ Atom "declare-const",
            Atom "x_0",
            List [Atom "_", Atom "BitVec", Atom "32"]
          ],
        List
          [ Atom "declare-const",
            Atom "x_1",
            List [Atom "_", Atom "BitVec", Atom "32"]
          ],
        List
          [ Atom "declare-const",
            Atom "x_2",
            List [Atom "_", Atom "BitVec", Atom "32"]
          ],
        List
          [ Atom "declare-const",
            Atom "y_0",
            List [Atom "_", Atom "BitVec", Atom "32"]
          ],
        List
          [ Atom "declare-const",
            Atom "y_1",
            List [Atom "_", Atom "BitVec", Atom "32"]
          ],
        List
          [ Atom "assert",
            List
              [Atom "=", Atom "x_1", List [Atom "bvadd", Atom "x_0", Atom "y_0"]]
          ],
        List
          [ Atom "assert",
            List
              [Atom "=", Atom "y_1", List [Atom "bvsub", Atom "x_1", Atom "y_0"]]
          ],
        List
          [ Atom "assert",
            List
              [Atom "=", Atom "x_2", List [Atom "bvsub", Atom "x_1", Atom "y_1"]]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "not",
                List
                  [ Atom "and",
                    List [Atom "=", Atom "x_2", Atom "y_0"],
                    List [Atom "=", Atom "y_1", Atom "x_0"]
                  ]
              ]
          ],
        List [Atom "check-sat"],
        List [Atom "exit"]
      ],
    Example
      "scopes"
      [r|
      ; Using scopes to explore multiple problems
      (set-logic QF_LIA)
      (declare-const x Int) (declare-const y Int)
      (assert (= (+ x (* 2 y)) 20))
      (push 1)
          (assert (= (- x y) 2))
          (check-sat)
          ; sat
      (pop 1)
      (push 1)
          (assert (= (- x y) 3))
          (check-sat)
          ; unsat
      (pop 1)
      (exit)
      |]
      [ List [Atom "set-logic", Atom "QF_LIA"],
        List [Atom "declare-const", Atom "x", Atom "Int"],
        List [Atom "declare-const", Atom "y", Atom "Int"],
        List
          [ Atom "assert",
            List
              [ Atom "=",
                List [Atom "+", Atom "x", List [Atom "*", Atom "2", Atom "y"]],
                Atom "20"
              ]
          ],
        List [Atom "push", Atom "1"],
        List
          [ Atom "assert",
            List [Atom "=", List [Atom "-", Atom "x", Atom "y"], Atom "2"]
          ],
        List [Atom "check-sat"],
        List [Atom "pop", Atom "1"],
        List [Atom "push", Atom "1"],
        List
          [ Atom "assert",
            List [Atom "=", List [Atom "-", Atom "x", Atom "y"], Atom "3"]
          ],
        List [Atom "check-sat"],
        List [Atom "pop", Atom "1"],
        List [Atom "exit"]
      ],
    Example
      "sorts"
      [r|
      ; Defining and using new sorts
      (set-logic QF_UF)
      (declare-sort A 0)
      (declare-const a A) (declare-const b A) (declare-const c A)
      (declare-const d A) (declare-const e A)
      (assert (or (= c a)(= c b)))
      (assert (or (= d a)(= d b)))
      (assert (or (= e a)(= e b)))
      (push 1)
          (assert (distinct c d))
          (check-sat)
          ; sat
      (pop 1)
      (push 1)
          (assert (distinct c d e))
          (check-sat)
          ; unsat
      (pop 1)
      (exit)
      |]
      [ List [Atom "set-logic", Atom "QF_UF"],
        List [Atom "declare-sort", Atom "A", Atom "0"],
        List [Atom "declare-const", Atom "a", Atom "A"],
        List [Atom "declare-const", Atom "b", Atom "A"],
        List [Atom "declare-const", Atom "c", Atom "A"],
        List [Atom "declare-const", Atom "d", Atom "A"],
        List [Atom "declare-const", Atom "e", Atom "A"],
        List
          [ Atom "assert",
            List
              [ Atom "or",
                List [Atom "=", Atom "c", Atom "a"],
                List [Atom "=", Atom "c", Atom "b"]
              ]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "or",
                List [Atom "=", Atom "d", Atom "a"],
                List [Atom "=", Atom "d", Atom "b"]
              ]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "or",
                List [Atom "=", Atom "e", Atom "a"],
                List [Atom "=", Atom "e", Atom "b"]
              ]
          ],
        List [Atom "push", Atom "1"],
        List [Atom "assert", List [Atom "distinct", Atom "c", Atom "d"]],
        List [Atom "check-sat"],
        List [Atom "pop", Atom "1"],
        List [Atom "push", Atom "1"],
        List [Atom "assert", List [Atom "distinct", Atom "c", Atom "d", Atom "e"]],
        List [Atom "check-sat"],
        List [Atom "pop", Atom "1"],
        List [Atom "exit"]
      ],
    Example
      "unsat cores"
      [r|
      ; Getting unsatisfiable cores
      (set-option :produce-unsat-cores true)
      (set-logic QF_UF)
      (declare-const p Bool) (declare-const q Bool) (declare-const r Bool)
      (declare-const s Bool) (declare-const t Bool)
      (assert (! (=> p q) :named PQ))
      (assert (! (=> q r) :named QR))
      (assert (! (=> r s) :named RS))
      (assert (! (=> s t) :named ST))
      (assert (! (not (=> q s)) :named NQS))
      (check-sat)
      ; unsat
      (get-unsat-core)
      ; (QR RS NQS)
      (exit)
      |]
      [ List [Atom "set-option", Atom ":produce-unsat-cores", Atom "true"],
        List [Atom "set-logic", Atom "QF_UF"],
        List [Atom "declare-const", Atom "p", Atom "Bool"],
        List [Atom "declare-const", Atom "q", Atom "Bool"],
        List [Atom "declare-const", Atom "r", Atom "Bool"],
        List [Atom "declare-const", Atom "s", Atom "Bool"],
        List [Atom "declare-const", Atom "t", Atom "Bool"],
        List
          [ Atom "assert",
            List
              [ Atom "!",
                List [Atom "=>", Atom "p", Atom "q"],
                Atom ":named",
                Atom "PQ"
              ]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "!",
                List [Atom "=>", Atom "q", Atom "r"],
                Atom ":named",
                Atom "QR"
              ]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "!",
                List [Atom "=>", Atom "r", Atom "s"],
                Atom ":named",
                Atom "RS"
              ]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "!",
                List [Atom "=>", Atom "s", Atom "t"],
                Atom ":named",
                Atom "ST"
              ]
          ],
        List
          [ Atom "assert",
            List
              [ Atom "!",
                List [Atom "not", List [Atom "=>", Atom "q", Atom "s"]],
                Atom ":named",
                Atom "NQS"
              ]
          ],
        List [Atom "check-sat"],
        List [Atom "get-unsat-core"],
        List [Atom "exit"]
      ],
    Example
      "values or models"
      [r|
      ; Getting values or models
      (set-option :produce-models true)
      (set-logic QF_LIA)
      (declare-const x Int)
      (declare-const y Int)
      (assert (= (+ x (* 2 y)) 20))
      (assert (= (- x y) 2))
      (check-sat)
      ; sat
      (get-value (x y))
      ; ((x 8) (y 6))
      (get-model)
      ; ((define-fun x () Int 8)
      ;  (define-fun y () Int 6)
      ; )
      (exit)
      |]
      [ List [Atom "set-option", Atom ":produce-models", Atom "true"],
        List [Atom "set-logic", Atom "QF_LIA"],
        List [Atom "declare-const", Atom "x", Atom "Int"],
        List [Atom "declare-const", Atom "y", Atom "Int"],
        List
          [ Atom "assert",
            List
              [ Atom "=",
                List [Atom "+", Atom "x", List [Atom "*", Atom "2", Atom "y"]],
                Atom "20"
              ]
          ],
        List
          [ Atom "assert",
            List [Atom "=", List [Atom "-", Atom "x", Atom "y"], Atom "2"]
          ],
        List [Atom "check-sat"],
        List [Atom "get-value", List [Atom "x", Atom "y"]],
        List [Atom "get-model"],
        List [Atom "exit"]
      ],
    Example
      "z3 error"
      "(error \"line 1 column 33: invalid command, '(' expected\")"
      [ List
          [ Atom "error",
            Atom "\"line 1 column 33: invalid command, '(' expected\""
          ]
      ],
    Example
      "terms"
      [r|
          ; hexadecimals
          #x0 #xA04
          #x01Ab #x61ff
          ; binaries
          #b0 #b1
          #b001 #b101011
          ; string literals
          "this is a string literal"
          ""
          "She said : ""Bye bye"" and left."
          "this is a string literal
          with a line break in it"
          ; symbols
          + <= x plus ** $ <sas <adf>
          abc77 *$s&6 .kkk .8 +34 -32
          |this is a quoted symbol|
          |so is
          this one|
          ||
          | " can occur too|
          |af klj^*0asfe2(&*)&(#^$>>>?"']]984|
          ; keywords
          :date :a2 :foo-bar
          :<= :56 :->
          |]
      [ Atom "#x0",
        Atom "#xA04",
        Atom "#x01Ab",
        Atom "#x61ff",
        Atom "#b0",
        Atom "#b1",
        Atom "#b001",
        Atom "#b101011",
        Atom "\"this is a string literal\"",
        Atom "\"\"",
        Atom "\"She said : \"\"Bye bye\"\" and left.\"",
        Atom "\"this is a string literal\n          with a line break in it\"",
        Atom "+",
        Atom "<=",
        Atom "x",
        Atom "plus",
        Atom "**",
        Atom "$",
        Atom "<sas",
        Atom "<adf>",
        Atom "abc77",
        Atom "*$s&6",
        Atom ".kkk",
        Atom ".8",
        Atom "+34",
        Atom "-32",
        Atom "|this is a quoted symbol|",
        Atom "|so is\n          this one|",
        Atom "||",
        Atom "| \" can occur too|",
        Atom "|af klj^*0asfe2(&*)&(#^$>>>?\"']]984|",
        Atom ":date",
        Atom ":a2",
        Atom ":foo-bar",
        Atom ":<=",
        Atom ":56",
        Atom ":->"
      ]
  ]
