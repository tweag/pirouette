---- MODULE Contract_MC ----
EXTENDS Contract, TLC, FiniteSets

CONSTANTS
  bs1, bs2, bs3, bs4, bs5, s1,s2,s3,s4

instance_PlutusByteString == {s1,s2,s3,s4}
symm_PlutusByteString == Permutations(instance_PlutusByteString)

instance_PlutusSignature == {s1, s2, s3, s4}

instance_ParamSigners == Cons(s1, Cons(s2, Cons(s3, Nil)))
instance_ParamN == 2

RECURSIVE ListToSet(_)
ListToSet(xs) == Nil_match(xs, {}, LAMBDA x, xxs: { x } \union ListToSet(xxs))

RECURSIVE ListHas(_,_)
ListHas(f(_), xs) == Nil_match(xs, FALSE, LAMBDA x, xxs: f(x) \/ ListHas(f, xxs))

MustPayTo(n) == n.cons = "MustPayToPubKey"

Ideal == INSTANCE ContractSpec
         WITH st_Holding    <- "H"
            , st_Collecting <- "C"
            , Signers       <- ListToSet(param.arg0)
            , N             <- param.arg1
            , st            <- MSState_match(st.arg0, LAMBDA x,xs: "C", "H")
            , sigs          <- MSState_match(st.arg0, LAMBDA x,xs: ListToSet(xs), {})
            , payed         <- ListHas(MustPayTo,txConstr.arg0)
IdealSpec == Ideal!Spec

StateConstraint == TRUE

PayCorrect == [](ENABLED ActionPay => Cardinality(ListToSet(st.arg0.arg1)) >= param.arg1)

====
