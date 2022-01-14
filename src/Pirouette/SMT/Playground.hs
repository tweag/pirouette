module Pirouette.SMT.Playground where

import Pirouette.SMT.Common
import qualified Pirouette.SMT.SimpleSMT as SmtLib

-- Manually translated ADT definition from the following PIR example
--
-- (datatypebind
--   (datatype
--     (tyvardecl List_26677 (fun (type) (type)))
--     (tyvardecl a_26681 (type))
--     Nil_match_26680
--     (vardecl Nil_26678 [ List_26677 a_26681 ])
--     (vardecl
--       Cons_26679
--       (fun a_26681 (fun [ List_26677 a_26681 ] [ List_26677 a_26681 ]))
--     )
--   )
-- )
declareDatatypeList :: SmtLib.Solver -> IO ()
declareDatatypeList s =
  SmtLib.declareDatatype
    s
    "List_26677"
    ["a_26681"]
    [ ("Nil_26678", []),
      ("Cons_26679", [("Cons_26679_1", SmtLib.symbol "a_26681"), ("Cons_26679_2", SmtLib.app (SmtLib.symbol "List_26677") [SmtLib.symbol "a_26681"])])
    ]

-- | Proof of concept: define some datatypes, values, constraints on values,
-- and check if sat
adtProofOfConcept :: IO ()
adtProofOfConcept =
  do
    s <- prepareSMT
    SmtLib.declareDatatype
      s
      "Maybe"
      ["a"]
      [("Just", [("elem", SmtLib.symbol "a")]), ("Nothing", [])]
    SmtLib.declareDatatype
      s
      "Day"
      []
      [ ("Monday", []),
        ("Tuesday", []),
        ("Wednesday", []),
        ("Thursday", []),
        ("Friday", []),
        ("Saturday", []),
        ("Sunday", [])
      ]
    SmtLib.declareDatatype
      s
      "Couple"
      ["a", "b"]
      [("Couple", [("fst", SmtLib.symbol "a"), ("snd", SmtLib.symbol "b")])]

    x <-
      SmtLib.declare s "x" $
        SmtLib.app
          (SmtLib.symbol "Maybe")
          [ SmtLib.app
              (SmtLib.symbol "Couple")
              [SmtLib.symbol "Day", SmtLib.tInt]
          ]
    y <- SmtLib.declare s "y" (SmtLib.symbol "Day")
    z <- SmtLib.declare s "z" SmtLib.tInt

    SmtLib.assert
      s
      ( SmtLib.not $
          SmtLib.orMany
            [ y `SmtLib.eq` SmtLib.symbol "Monday",
              y `SmtLib.eq` SmtLib.symbol "Tuesday",
              y `SmtLib.eq` SmtLib.symbol "Wednesday"
            ]
      )
    SmtLib.assert s (z `SmtLib.gt` SmtLib.int 5)
    SmtLib.assert
      s
      ( x
          `SmtLib.eq` SmtLib.app
            (SmtLib.symbol "Just")
            [SmtLib.app (SmtLib.symbol "Couple") [y, z]]
      )

    print =<< SmtLib.check s
    print =<< SmtLib.getExprs s [x]
