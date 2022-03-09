(program
  (let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl List (fun (type) (type)))
        (tyvardecl a (type))
        Nil_match
        (vardecl Nil [List a]) (vardecl Cons (fun a (fun [List a] [List a])))
    ))
    (datatypebind
      (datatype
        (tyvardecl Maybe (fun (type) (type)))
        (tyvardecl a (type))
        Maybe_match
        (vardecl Nothing [Maybe a]) (vardecl Just (fun a [Maybe a]))
    ))
    (datatypebind
      (datatype
        (tyvardecl Unit (type))
        Unit_match
        (vardecl TT Unit)
    ))
    (datatypebind
      (datatype
        (tyvardecl Peano (type))
        Peano_match
        (vardecl Z Peano) (vardecl S (fun Peano Peano))
    ))
    (datatypebind
      (datatype
        (tyvardecl Bool (type))
        Bool_match
        (vardecl True Bool) (vardecl False Bool)
    ))
    (datatypebind
      (datatype
        (tyvardecl Input (type))
        Input_match
        (vardecl InputAppend   (fun Bool Input)) 
        (vardecl InputConst    (fun Bool Input)) 
        (vardecl InputCompress Input) 
    ))
    (datatypebind
      (datatype
        (tyvardecl State (type))
        State_match
        (vardecl St (fun [List Bool] State))
    ))
    (termbind 
      (strict)
      (vardecl init_state State)
      [St { Nil Bool }]
    )
    (termbind
      (strict)
      (vardecl id (all a (type) (fun a a)))
      (abs a (type) (lam i a i))
    )
    (termbind
      (strict)
      (vardecl const (all a (type) (all b (type) (fun a (fun b a)))))
      (abs a (type) (abs b (type) (lam xa a (lam xb b xa))))
    )
    (termbind
      (strict)
      (vardecl bor (fun Bool (fun Bool Bool)))
      (lam b0 Bool 
        [[{[ Bool_match b0 ] (fun Bool Bool)}
          [{{const Bool} Bool} True] ]
          {id Bool} ]
    ))
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
      (vardecl fold (all a (type) (fun [Monoid a] (fun [List a] a))))
      (abs a (type) (lam mon [Monoid a] (lam lss [List a]
        [{[ { Monoid_match a } mon] a} 
          (lam f (fun a (fun a a)) (lam z a
            [[{[{Nil_match a } lss] a }
              z ]
              (lam l a (lam ls [List a]
                [[f l] [[ {fold a} mon] ls]]
                ))]))
        ]
      ))))
    (termbind
      (strict)
      (vardecl bad_name (fun Bool (fun Bool Bool)))
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
      (vardecl
        p1AdditiveMonoid
        (all a (type) (fun [AdditiveMonoid a] (fun a (fun a a))))
      )
      (abs a (type)
        (lam v [AdditiveMonoid a]
          [ { [ { AdditiveMonoid_match a } v ] (fun a (fun a a)) }
            (lam v_160 (fun a (fun a a)) (lam v_162 a v_160))
          ]
        )
      )
    )
    (termbind
      (strict)
      (vardecl zero (all a (type) (fun [AdditiveMonoid a] a)))
      (abs a (type) (lam v [AdditiveMonoid a]
          [ { [ { AdditiveMonoid_match a } v ] a }
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
          [ [ { CConsMonoid a }
              (lam eta_169 a
                (lam eta_171 a
                  [ [ [ { p1AdditiveMonoid a } v ]
                      eta_169 ]
                      eta_171 ]
                )) ] 
            [ { zero a } v ]
          ]))
    )
    (termbind
      (nonstrict)
      (vardecl fAdditiveMonoidBool [AdditiveMonoid Bool])
      [ [ { CConsAdditiveMonoid Bool } bad_name ] False ]
    )
    (termbind
      (strict)
      (vardecl or (fun [List Bool] Bool))
      (lam iss [List Bool]
          [[{fold Bool} [{fMonoidSum Bool} fAdditiveMonoidBool]] iss]
      )
    )
    (termbind
      (strict)
      (vardecl length (all a (type) (fun [List a] Peano)))
      (abs a (type) (lam xss [List a]
          [[{[{ Nil_match a } xss ] Peano }
              Z]
              (lam x a (lam xs [List a] [S [{length a} xs]] ))]
      ))
    )
    (termbind
      (strict)
      (vardecl iterate (all a (type) (fun (fun a a) (fun a (fun Peano a)))))
      (abs a (type) (lam f (fun a a) (lam s a (lam n Peano
          [[{ [ Peano_match n ] a } 
            s ]
            (lam nMinus1 Peano [f [[[{ iterate a } f] s] nMinus1 ] ] )]
      ))))
    )
    (termbind 
      (strict)
        (vardecl transition (fun Input (fun State [Maybe State])))
        (lam i Input (lam st State
          [{[State_match st] [Maybe State]}
            (lam bs [List Bool]
              [[[{[Input_match i] [Maybe State]}
                  (lam x Bool [{Just State} [St [[{Cons Bool} x] bs]]] )]
                  (lam x Bool [{Just State} [St [
                    [[{ iterate [List Bool] } [{Cons Bool} x]] {Nil Bool}] [{length Bool} bs] ]]] )] 
                  [[{[{ Nil_match Bool } bs] [Maybe State]} 
                      {Nothing State}]
                      (lam b0 Bool (lam bs0 [List Bool] 
                        [{Just State} [St [{Cons Bool} [or bs] { Nil Bool } ]]]
                      ))]
                ]
                  
          )]
    )))
    (termbind (strict)
      (vardecl main [Maybe State])
      [[transition InputCompress] init_state]
    )      
    main
))
