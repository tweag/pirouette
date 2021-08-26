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
      (datatypebind
          (datatype
            (tyvardecl FirstSecond (type))
            FS_match
            (vardecl First FirstSecond) (vardecl Second FirstSecond)
          )
      )
      (termbind
        (strict)
        (vardecl
          problem
          (fun FirstSecond (fun FirstSecond Bool))
        )
        (lam
          arg_721
          FirstSecond
          (lam
            arg_722
            FirstSecond
            (let
              (nonrec)
              (termbind
                (strict)
                (vardecl b_723 (con bool))
                [
                  [ (builtin greaterThanEqualsInteger) arg_721 ]
                  arg_722
                ]
              )
              [
                [ [ { (builtin ifThenElse) Bool } b_723 ] True ]
                False
              ]
            )
          )
        )
      )
      (termbind (strict)
        (vardecl main Bool)
        [problem First Second])
      main
  )
)

