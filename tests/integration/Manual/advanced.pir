(program
  (let
    (rec)
     (datatypebind
        (datatype
          (tyvardecl Unit (type))
          Unit_match
          (vardecl TT Unit)
        )
     )
     (datatypebind
        (datatype
          (tyvardecl Bool (type))
          Bool_match
          (vardecl True Bool) (vardecl False Bool)
        )
      )
      (datatypebind
        (datatype
          (tyvardecl Input (type))
          Input_match
          (vardecl And Input) (vardecl Or Input)
        )
      )
      (datatypebind
        (datatype
          (tyvardecl Square (fun (type) (type)))
          (tyvardecl a (type))
          Square_match
          (vardecl Pair (fun a (fun a [Square a])))
        )
      )
      (datatypebind
        (datatype
          (tyvardecl AdditiveMonoid (fun (type) (type)))
          (tyvardecl a (type))
          AdditiveMonoid_match
          (vardecl CConsAdditiveMonoid (fun (fun a (fun a a)) (fun a [AdditiveMonoid a])))
        )
      )
      (datatypebind
        (datatype
          (tyvardecl Monoid (fun (type) (type)))
          (tyvardecl a (type))
          Monoid_match
          (vardecl CConsMonoid (fun (fun a (fun a a)) (fun a [Monoid a])))
        )
      )
      (termbind
        (strict)
        (vardecl or (fun Bool (fun Bool Bool)))
        (lam ds_8 Bool (lam ds_9 Bool
            [ [ [ { [ Bool_match ds_8 ] (fun Unit Bool) }
                  (lam thunk_10 Unit True)
                ]
                (lam thunk_11 Unit ds_9)
              ]
              TT
            ]
          )
        )
      )
      (termbind
        (strict)
        (vardecl and (fun Bool (fun Bool Bool)))
        (lam ds_8 Bool (lam ds_9 Bool
            [ [ [ { [ Bool_match ds_8 ] (fun Unit Bool) }
                  (lam thunk_10 Unit ds_9)
                ]
                (lam thunk_11 Unit False)
              ]
              TT
            ]
          )
        )
      )
      (termbind
        (strict)
        (vardecl
          p1Monoid
          (all a (type) (fun [Monoid a] (fun a (fun a a))))
        )
        (abs a (type)
          (lam v [Monoid a]
            [ { [ { Monoid_match a } v ] (fun a (fun a a)) }
              (lam v_160 (fun a (fun a a)) (lam v_162 a v_160))
            ]
          )
        )
      )
      (termbind
        (strict)
        (vardecl zero (all a (type) (fun [Monoid a] a)))
        (abs a (type) (lam v [Monoid a]
            [ { [ { Monoid_match a } v ] a }
              (lam v_21 (fun a (fun a a)) (lam v_23 a v_23))
            ]
          )
        )
      )
      (termbind
        (strict)
        (vardecl fMonoidSum
          (all a (type) (fun [AdditiveMonoid a] [Monoid a]))
        )
        (abs a (type)
          (lam v [AdditiveMonoid a]
            [ { [ { AdditiveMonoid_match a } v ] [Monoid a] }
              (lam op (fun a (fun a a))
                (lam z a
                  [[CConsMonoid op] z]
                )
              )
            ]
          )
        )
      )
      (termbind
        (nonstrict)
        (vardecl orAdditiveMonoid [AdditiveMonoid Bool])
        [ [ { CConsAdditiveMonoid Bool } or ] False ]
      )
      (termbind
        (nonstrict)
        (vardecl andAdditiveMonoid [AdditiveMonoid Bool])
        [ [ { CConsAdditiveMonoid Bool } and ] True ]
      )
      (termbind
        (strict)
        (vardecl transition (fun Input (fun [Square Bool] [Square Bool])))
        (lam i Input
          (lam sq [Square Bool]
            [{[{Square_match Bool} sq] [Square Bool]}
              (lam b1 Bool
                (lam b2 Bool
                  [[{[Input_match i] [Square Bool]}
                    (let (nonrec)
                      (termbind (strict)
                        (vardecl mono [Monoid Bool])
                        [{ fMonoidSum Bool } andAdditiveMonoid ]
                      )
                      [[{Pair Bool}
                        [[[{p1Monoid Bool} mono] b1] b2]]
                        [{zero Bool} mono]
                      ]
                    )]
                    (let (nonrec)
                      (termbind (strict)
                        (vardecl mono [Monoid Bool])
                        [{ fMonoidSum Bool } orAdditiveMonoid ]
                      )
                      [[{Pair Bool}
                        [[[{p1Monoid Bool} mono] b1] b2]]
                        [{zero Bool} mono]
                      ]
                    )
                  ]
                )
              )
            ]
          )
        )
      )
      TT
  )
)

