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
    (termbind
      (strict)
      (vardecl three Peano)
      [S [S [S Z]]]
    )
    (termbind
      (strict)
      (vardecl psum (fun Peano (fun Peano Peano)))
      (lam x Peano (lam y Peano
        [[ {[ Peano_match x ] Peano }
           y]
           (lam px Peano [S [[psum px] y]]) ]
    )))
    (datatypebind
      (datatype
        (tyvardecl Bool (type))
        Bool_match
        (vardecl True Bool) (vardecl False Bool)
    ))
    (termbind
      (strict)
      (vardecl leq (fun Peano (fun Peano Bool)))
      (lam x Peano (lam y Peano
        [[{[Peano_match x] Bool }
           True ]
           (lam sx Peano 
             [[{[Peano_match y] Bool } 
                False ]
                (lam sy Peano [[leq sx] sy]) ]
           )]
    )))
    (datatypebind
      (datatype
        (tyvardecl Input (type))
        Input_match
        (vardecl InputA  (fun Peano Input)) 
    ))
    (datatypebind
      (datatype
        (tyvardecl State (type))
        State_match
        (vardecl St (fun [List Peano] State))
    ))
    (termbind 
      (strict)
      (vardecl init_state State)
      [St { Nil [List Peano] }]
    )
    (termbind
      (strict)
      (vardecl foldr (all a (type) (all b (type) (fun (fun a (fun b b)) (fun b (fun [List a] b))))))
      (abs a (type) (abs b (type) (lam f (fun a (fun b b)) (lam e b (lam xs [List a]
        [[{[ { Nil_match a } xs ] b }
           e]
           (lam xa a (lam xas [List a] [[f xa] [[[{{ foldr a } b } f ] e ] xas]] ))]
    ))))))
    (termbind
      (strict)
      (vardecl sumWith (fun Peano (fun [List Peano] Peano)))
      (lam i Peano [[{{ foldr Peano } Peano } (lam h Peano (lam r Peano [[psum h] [psum i r]])) ] Z ])
    )
    (termbind
      (strict)
      (vardecl length (fun [List Peano] Peano))
      [[{{ foldr Peano } Peano } (lam h Peano S) ] Z ]
    )
    (termbind 
      (strict)
        (vardecl goInputA (fun [List Peano] (fun Peano [List Peano])))
        (lam bs [List Peano] (lam x Peano 
          [[ {[ Bool_match [[leq [length bs]] three]] [List Peano]}
              [[ { Cons Peano } x ] bs ] ]
              [[ { Cons Peano } [[sumWith x] bs] ] { Nil Peano } ] ]
    )))
    (termbind 
      (strict)
        (vardecl transition (fun Input (fun State [Maybe State])))
        (lam i Input (lam st State
          [{[State_match st] [Maybe State]}
            (lam bs [List Peano]
              [{[Input_match i] [Maybe State]}
                  (lam x Peano [Just [St [[goInputA bs] x]]] 
              )]
          )]
    )))
    (termbind (strict)
      (vardecl main [Maybe State])
      [[transition [InputA [S Z]]] init_state]
    )      
    main
))
