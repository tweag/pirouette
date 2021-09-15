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
        (tyvardecl Bool (type))
        Bool_match
        (vardecl True Bool) (vardecl False Bool)
    ))
    (datatypebind
      (datatype
        (tyvardecl Peano (type))
        Peano_match
        (vardecl Z Peano) (vardecl S (fun Peano Peano))
    ))
    (termbind
      (strict)
      (vardecl psum (fun Peano (fun Peano Peano)))
      (lam x Peano (lam y Peano
        [[ {[ Peano_match x ] Peano }
           y]
           (lam px Peano [S [[psum px] y]]) ]
    )))
    (termbind
      (strict)
      (vardecl pmul (fun Peano (fun Peano Peano)))
      (lam x Peano (lam y Peano
        [[ {[ Peano_match x ] Peano }
           Z]
           (lam px Peano [[psum y] [[pmul px] y]] ) ]
    )))
    (datatypebind
      (datatype
        (tyvardecl PeanoEndo (type))
        PeanoEndo_match
        (vardecl PE (fun (fun Peano Peano) PeanoEndo))
    ))
    (termbind
      (strict)
      (vardecl peApply (fun PeanoEndo (fun Peano Peano)))
      (lam x PeanoEndo (lam y Peano
        [ { [ PeanoEndo_match x ] Peano }
          (lam f (fun Peano Peano) [f y]) ]
    )))
    (termbind
      (strict)
      (vardecl twoPossiblePeanoEndos (fun Peano (fun Bool PeanoEndo)))
      (lam freeV Peano (lam choice Bool
        [[ { [ Bool_match choice ] PeanoEndo }
           [ PE (lam y Peano [[psum y] freeV]) ] ]
           [ PE (lam y Peano [[pmul y] freeV]) ] ]
    )))
    (datatypebind
      (datatype
        (tyvardecl Input (type))
        Input_match
        (vardecl Execute (fun Peano (fun Bool Input))) 
    ))
    (datatypebind
      (datatype
        (tyvardecl State (type))
        State_match
        (vardecl St (fun Peano State))
    ))
    (termbind 
      (strict)
      (vardecl init_state State)
      [St Z]
    )
    (termbind 
      (strict)
        (vardecl transition (fun Input (fun State State)))
        (lam i Input (lam st State
          [{[State_match st] State}
            (lam xSt Peano
              [{[Input_match i] State}
                  (lam x Peano (lam c Bool [St [[peApply [[twoPossiblePeanoEndos x] c]] xSt]]
              ))]
          )]
    )))
    (termbind (strict)
      (vardecl main State)
      [[transition [[Execute [S Z]] True]] init_state]
    )      
    main
))
