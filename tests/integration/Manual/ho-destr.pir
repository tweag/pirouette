(program
  (let
    (rec)
      (datatypebind
          (datatype
            (tyvardecl ABC (type))
            ABC_match
            (vardecl A ABC) (vardecl B ABC) (vardecl C ABC)
          )
      )
      (datatypebind
          (datatype
            (tyvardecl State (type))
            State_match
            (vardecl Zero State)
            (vardecl Inc (fun State State))
            (vardecl Dec (fun State State))
          )
      )
      (termbind
        (strict)
        (vardecl id (all a (type) (fun a a)))
        (abs a (type) (lam i a i)))
      (termbind
        (strict)
        (vardecl transition (fun ABC (fun State State)))
        (lam i ABC (lam st State
          [[[[{[ ABC_match i ] (fun State State) }
             Inc ]
             Dec ]
             {id State} ]
             st ]
        ))
      )
      A
  )
)

