(program
  (let
    (rec)
      (datatypebind
          (datatype
            (tyvardecl Bool (type))
            Bool_match
            (vardecl True Bool) (vardecl False Bool)
          )
      )
      (termbind 
        (strict)
        (vardecl not (fun Bool Bool))
        (lam a Bool
          [[ { [ Bool_match a ] Bool }
             False ]
             True  ]
      ))
      (termbind 
        (strict)
        (vardecl or (fun Bool (fun Bool Bool)))
        (lam a Bool (lam b Bool
          [[ { [ Bool_match a ] Bool }
             True ]
             b    ]
      )))
      (termbind
        (strict) 
        (vardecl top (fun Bool (fun Bool Bool)))
        (lam xxx Bool
          (let
            (nonrec)
            (termbind
              (strict)
              (vardecl dsdsds Bool)
              [not xxx])
            (termbind
              (strict)
              (vardecl mmm Bool)
              [not rrr])
            (termbind
              (strict)
              (vardecl rrr Bool)
              [not dsdsds])
            (lam nnn Bool
              (let
                (nonrec)
                (termbind 
                  (strict)
                  (vardecl jjj Bool)
                  [[or nnn] mmm])
                jjj
            )))
      ))
      top)
)

