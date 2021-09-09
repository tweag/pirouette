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
        (vardecl defaultId (all s (type) (fun [Maybe (fun s s)] (fun s s))))
        (abs s (type) (lam f [Maybe (fun s s)] (lam st s
          [[ { [ { Maybe_match (fun s s) } f ] s }
            (lam x (fun s s) [x st]) ]
            st ]
        )))
      )
      (termbind
        (strict)
        (vardecl transition (fun State (fun Input State)))
        (lam s State
          (lam i Input
            [{[[[{[Input_match i] (all s (type) (fun s s))}
               (abs s (type) [{ defaultId s } Nothing])]
               (abs s (type) [{ defaultId s } [Just Inc]])]
               (abs s (type) [{ defaultId s } [Just Dec]])]
               State }
               s
            ]
          )
        )
      )
      Zero
  )
)

