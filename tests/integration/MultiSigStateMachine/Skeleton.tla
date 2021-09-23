---- MODULE Contract ----
EXTENDS Integers, TLC, Sequences
VARIABLE st,txConstr
CONSTANT MAXDEPTH, PlutusByteString, ParamSigners, ParamN

vars ==
  <<st,txConstr>>

PlutusInteger ==
  0..6

PlutusData == {}

fst(tup) == tup[1]

snd(tup) == tup[2]

----
----

Init ==
  /\ txConstr = TxConstraints1(Nil,Nil,Nil)
  /\ st = State1(Holding,Nil)

Spec ==
  Init /\ []([Next]_vars) /\ WF_vars(Next)

RECURSIVE len(_)
len(xs) ==
  Nil_match(xs,0,LAMBDA i22,is31 : 1+len(is31))

SillyInv == [](~((st.arg0.cons = "CollectingSignatures" /\ len(st.arg0.arg1) = 1)))
====
