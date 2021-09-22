---- MODULE Game ----
EXTENDS Integers, Sequences
VARIABLE st,txConstr
CONSTANT MAXDEPTH, mPol, tok, pk1, pk2, pk3, pk4, pk5
vars ==
  <<st,txConstr>>
PlutusInteger == 0..6
PlutusByteString == {pk1, pk2, pk3, pk4, pk5}
SHA2(x) == x

RECURSIVE PlutusDataBounded(_)
PlutusDataBounded(n) == 
  IF n = 0
  THEN {}
  ELSE [ cons : {"Constr"}, arg0 : PlutusInteger, arg1 : PlutusDataBounded(n-1) ]

PlutusData == UNION { PlutusDataBounded(n) : n \in 0 .. MAXDEPTH }

ConstrData(n,i) == [cons |-> "Constr", arg0 |-> n, arg1 |-> i]
MkNilData(x) == [cons |-> "Nil" ]

fst(tup) == tup[1]

snd(tup) == tup[2]

----
----

Init ==
  /\ txConstr = TxConstraints1(Nil, Nil, Nil)
  /\ st = State1(Initialised(mPol,tok,pk3), Nil)
Spec ==
  Init /\ []([Next]_vars) /\ WF_vars(Next)

Inv == (st.arg0.cons = "Locked") ~> [](st.arg0.cons = "Initialised")
====
