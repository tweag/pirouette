import qualified Language.Pirouette.ExampleSpec as Ex
import qualified Pirouette.Symbolic.EvalSpec as SymbolicEval
import qualified Pirouette.Symbolic.ProveSpec as SymbolicProve
import qualified Pirouette.Term.Syntax.BaseSpec as Base
import qualified Pirouette.Term.Syntax.SystemFSpec as SF
import qualified Pirouette.Transformations.DefunctionalizationSpec as Defunc
import qualified Pirouette.Transformations.EtaExpandSpec as Eta
import qualified Pirouette.Transformations.MonomorphizationSpec as Mono
import qualified Pirouette.Transformations.PrenexSpec as Prenex
import qualified Pirouette.Transformations.TermSpec as Tr
import Test.Tasty
import qualified UnionFind.Spec as UF

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Pirouette"
    [ testGroup "SystemF" SF.tests,
      testGroup
        "Transformations"
        [ testGroup "Defunctionalization" Defunc.tests,
          testGroup "EtaExpand" Eta.tests,
          testGroup "Monomorphization" Mono.tests,
          testGroup "Prenex" Prenex.tests,
          testGroup "Term" Tr.tests
        ],
      testGroup
        "Term"
        [testGroup "Base" Base.tests],
      testGroup
        "Symbolic"
        [ testGroup "Symbolic evaluation" SymbolicEval.tests,
          testGroup "Symbolic prove" SymbolicProve.tests
        ],
      testGroup
        "Language"
        [testGroup "Example" Ex.tests],
      testGroup "UnionFind" UF.tests
    ]
