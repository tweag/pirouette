---- MODULE IncDec ----

EXTENDS Integers, Sequences
VARIABLE st
CONSTANT MAXDEPTH

vars == << st >>

PlutusInteger == 0..6

PlutusByteString == {"a", "b"}

----
----

Init == st = State1(Counter1(0), 0)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Inv == [](st.arg0.arg0 >= 0)

StateConstraint == st.arg0.arg0 < 10

====
