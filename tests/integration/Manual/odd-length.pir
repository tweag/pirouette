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
            (vardecl dup (fun [List (con integer)] [List (con integer)]))
                (lam l [List (con integer)]
                    [{[{Nil_match (con integer)} l] [List (con integer)]}
                        {Nil (con integer)}
                        (lam head (con integer)
                            (lam tail [List (con integer)]
                              [{Cons (con integer)} head
                                [{Cons (con integer)} head
                                 [dup tail]
                                ]
                              ]
                            )
                        )
                    ]
                )
            )
        (termbind 
          (strict)
            (vardecl oddlength (fun [List (con integer)] Bool))
                (lam l [List (con integer)]
                    [{[{Nil_match (con integer)} l] Bool}
                        False
                        (lam Bhead (con integer)
                            (lam Btail [List (con integer)]
                                [{[{Nil_match (con integer)} Btail] Bool}
                                    True
                                    (lam Chead (con integer)
                                        (lam Ctail [List (con integer)]
                                            [oddlength Ctail]
                                        )
                                    )
                                ]
                            )
                        )
                    ]
            )
        )
    (lam x [List (con integer)] [oddlength [dup x]])
    )
  )
)
