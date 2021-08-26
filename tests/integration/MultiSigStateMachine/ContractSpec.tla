---- MODULE ContractSpec ----
EXTENDS FiniteSets, Naturals

CONSTANT st_Holding, st_Collecting, N, Signers
VARIABLE sigs, st, payed

vars == << sigs , st >>

ProposePayment 
  == st = st_Holding
  /\ st' = st_Collecting
  /\ sigs' = {}
  /\ payed' = FALSE

Pay 
  == st = st_Collecting
  /\ Cardinality(sigs) >= N
  /\ st' = st_Holding
  /\ sigs' = {}
  /\ payed' = TRUE

Cancel
  == st  = st_Collecting
  /\ st' = st_Holding
  /\ sigs' = {}
  /\ UNCHANGED payed


AddSig(s) 
  == st = st_Collecting
  /\ st' = st_Collecting
  /\ sigs' = { s } \union sigs
  /\ UNCHANGED payed

Next == ProposePayment
     \/ Pay
     \/ Cancel
     \/ (\E s \in Signers : AddSig(s))

Init == sigs = {}
     /\ st = st_Holding
     /\ payed = FALSE

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
