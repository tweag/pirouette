---- MODULE Game ----
EXTENDS Integers, Sequences
VARIABLE st,txConstr
CONSTANT MAXDEPTH, mPol, tok, pk1, pk2, pk3, pk4, pk5
vars ==
  <<st,txConstr>>
PlutusInteger == 0..6
PlutusByteString == {pk1, pk2, pk3, pk4, pk5}
SHA2(x) == x
----
----

Init ==
  /\ txConstr = TxConstraints1(Nil, Nil, Nil)
  /\ st = State1(Initialised(mPol,tok,pk3), Nil)
Spec ==
  Init /\ []([Next]_vars) /\ WF_vars(Next)

Inv == (st.arg0.cons = "Locked") ~> [](st.arg0.cons = "Initialised")
====
