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
    (termbind
      (strict)
      (vardecl id (all a (type) (fun a a)))
      (abs a (type) (lam i a i))
    )
    (let (rec)
        (termbind 
          (strict)
            (vardecl oddlength (fun [List (con integer)] Bool))
                (lam l [List (con integer)]
                    [{[{Nil_match (con integer)} l] Bool}
                        False
                        (lam head (con integer)
                            (lam tail [List (con integer)]
                                [{[{Nil_match (con integer)} tail] Bool}
                                    True
                                    (lam head2 (con integer)
                                        (lam tail2 [List (con integer)]
                                            [oddlength tail2]
                                        )
                                    )
                                ]
                            )
                        )
                    ]
            )
        )
    oddlength
    )
  )
)
