(program
  (let (rec)
    (datatypebind
      (datatype
        (tyvardecl Maybe (fun (type) (type)))
        (tyvardecl a (type))
        Maybe_match
        (vardecl Just (fun a [Maybe a]))
        (vardecl Nothing [Maybe a])
    ))
    (datatypebind
      (datatype
        (tyvardecl Either (fun (type) (fun (type) (type))))
        (tyvardecl a (type))
        (tyvardecl b (type))
        Either_match
        (vardecl Left  (fun a [Either a b]))
        (vardecl Right (fun b [Either a b]))
    ))
    (termbind (strict)
      (vardecl UNDEF tUNDEF)
      (lam p tp Nothing))
    (termbind (strict) (vardecl doSmthing tdoSmthing) (lam p tp UNDEF))
    (termbind (strict)
      (vardecl defaultNum tdefaultNum)
      (lam p tp UNDEF))
    (termbind (strict)
      (vardecl simple tmain)
      (lam p tp (lam q tp
        [doSmthing q [Maybe_match p (lam x tx [ [ (builtin addInteger) x ] x ]) defaultNum]])))
    (termbind (strict)
      (vardecl double tmain)
      (lam mx mmx (lam ey eey
        [doSmthing [Maybe_match mx (lam x tx [ [ (builtin addInteger) x ] x ]) defaultNum]
                   [Either_match ey (lam x tx defaultNum) (lam y ty [simple y])]
          ])))
    (termbind (strict)
      (vardecl swapDnfDouble tmain)
      (lam mx mmx (lam ey eey
        [Either_match ey 
          (lam y ty [Maybe_match mx (lam x tx [doSmthing [ [ (builtin addInteger) x ] x ] defaultNum])
                                    [doSmthing defaultNum defaultNum]])
          (lam y ty [Maybe_match mx (lam x tx [doSmthing [ [ (builtin addInteger) x ] x ] [simple y]])
                                    [doSmthing defaultNum [simple y]]])]

        )))
    (termbind (strict)
      (vardecl dnfDouble tmain)
      (lam mx mmx (lam ey eey
        [Maybe_match mx
            (lam x tx [Either_match ey (lam y ty [doSmthing [ [ (builtin addInteger) x ] x ] defaultNum])
                                       (lam y ty [doSmthing [ [ (builtin addInteger) x ] x ] [simple y]])])
            [Either_match ey (lam y ty [doSmthing defaultNum defaultNum])
                             (lam y ty [doSmthing defaultNum [simple y]])]
        ]
        )))
    main))
