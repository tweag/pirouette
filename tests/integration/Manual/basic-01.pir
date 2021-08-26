(program
  (let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl List (fun (type) (type)))
        (tyvardecl a (type))
        Nil_match
        (vardecl Nil [List a]) (vardecl Cons (fun a (fun [List a] [List a])))
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
        (vardecl ActionA Input) 
        (vardecl ActionB (fun Bool Input)) 
        (vardecl ActionC (fun [List Bool] (fun Bool Input))) 
      )
    )
    (termbind
      (strict)
      (vardecl id (all a (type) (fun a a)))
      (abs a (type) (lam i a i))
    )
    (termbind (strict)
      (vardecl main Bool)
      [[transition ActionA] False]
    )      
    (termbind 
      (strict)
        (vardecl transition (fun Input (fun Bool Bool)))
        (lam i Input (lam b Bool
          [[[{[ Input_match i ] Bool}
              b ]
              (lam x Bool b) ]
              (lam l [List Bool] (lam x Bool b)) ]
        ))
    )
    main
))
