(program
  (let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl Bool (type))
        Bool_match
        (vardecl True Bool) (vardecl False Bool)
    ))
    (datatypebind
      (datatype
        (tyvardecl List (fun (type) (type)))
        (tyvardecl a (type))
        Nil_match
        (vardecl Nil [List a]) (vardecl Cons (fun a (fun [List a] [List a])))
    ))
    (datatypebind
      (datatype
        (tyvardecl TxConstraint (type))
        TxConstraint_match
        (vardecl MustBeTrue (fun Bool TxConstraint))))
    (datatypebind
      (datatype
        (tyvardecl TxConstraints (fun (type) (fun (type) (type))))
        (tyvardecl a (type))
        (tyvardecl b (type))
        TxConstraints_match
        (vardecl TxConstraint (fun [List TxConstraint] [[TxConstraint a] b]))))
    (termbind
      (strict)
      (vardecl build (all a (type) (fun (all b (type) (fun (fun a (fun b b)) (fun b b))) [List a])))
      (abs a (type) (lam g (all b (type) (fun (fun a (fun b b)) (fun b b)))
        [ [ { g [List a] } { Cons a } ] { Nil a } ]
      )))
    (termbind
      (strict)
      (vardecl mustBeTrue (all a (type) (all b (type) (fun Bool [[TxConstraints a] b]))))
      (abs a (type) (abs b (type) (lam x Bool
        [ {{ TxConstraints a } b } 
          [ {build TxConstraint} 
            (abs k (type) (lam c (fun TxConstraint (fun k k)) (lam n k
             [[c [MustBeTrue x] ] n ]
            )))
          ]
        ]
      ))))
    (termbind 
      (strict)
        (vardecl prelong (fun Bool [[TxConstraints Bool] Bool]))
        (lam w Bool 
          [{{ mustBeTrue Bool } Bool } False]
        ))
    (termbind
      (strict)
        (vardecl long [[TxConstraints Bool] Bool])
        [prelong True]
    )
    (termbind
      (strict)
        (vardecl short [[TxConstraints Bool] Bool])
        [{{ TxConstraints Bool } Bool } 
          [[ { Cons TxConstraint } [MustBeTrue False] ] { Nil TxConstraint } ] ]
    )
    (termbind 
      (strict)
        (vardecl addone (fun (con integer) (con integer)))
        (lam x (con integer)
          [(builtin addInteger) x (con integer 1)]
        ))
    long
))
