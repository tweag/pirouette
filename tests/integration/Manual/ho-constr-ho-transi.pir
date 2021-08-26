(program
  (let
    (rec)
      (datatypebind
        (datatype
          (tyvardecl Maybe (fun (type) (type)))
          (tyvardecl a (type))
          Maybe_match
          (vardecl Just (fun a [Maybe a]))
          (vardecl Nothing [Maybe a])
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
      (datatypebind
        (datatype
          (tyvardecl Input (type))
          Input_match
          (vardecl N Input)
          (vardecl I Input)
          (vardecl D Input)
        )
      )
      (termbind
        (strict)
        (vardecl defaultId (fun [Maybe (fun State State)] (fun State State)))
        (lam f [Maybe (fun State State)] (lam st State
          [[ { [ { Maybe_match (fun State State) } f ] State }
            (lam x (fun State State) [x st]) ]
            st ]
        ))
      )
      (termbind
        (strict)
        (vardecl transition (fun Input (fun State State)))
        (lam i Input
          [[[{[Input_match i] (fun State State)}
            [defaultId Nothing]]
            [defaultId [Just Inc]]]
            [defaultId [Just Dec]]
          ]
        )
      )
      Zero
  )
)

