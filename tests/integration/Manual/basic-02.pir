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
        (tyvardecl Bool (type))
        Bool_match
        (vardecl True Bool) (vardecl False Bool)
    ))
    (datatypebind
      (datatype
        (tyvardecl Input (type))
        Input_match
        (vardecl InputAppend   (fun Bool Input)) 
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
    (termbind
      (strict)
      (vardecl or (fun [List Bool] Bool))
      (lam iss [List Bool]
        [[{[{ Nil_match Bool } iss ] Bool }
          False ]
          (lam i Bool (lam is [List Bool]
              [[bor i] [or is]]
          ))]
      )
    )
    (termbind 
      (strict)
        (vardecl transition (fun Input (fun State [Maybe State])))
        (lam i Input (lam st State
          [{[State_match st] [Maybe State]}
            (lam bs [List Bool]
              [[{[Input_match i] [Maybe State]}
                  (lam x Bool [Just [St [[{Cons Bool} x] bs]]] )]
                  [[{[{ Nil_match Bool } bs] [Maybe State]} 
                      Nothing]
                      (lam b0 Bool (lam bs0 [List Bool] 
                        [Just [St [{Cons Bool} [or bs] { Nil Bool } ]]]
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
