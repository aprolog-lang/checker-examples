(* SF:
Suppose instead that we add this rule:
      | T_Funny5 : 
            ⊢ tpred tzero ∈ TBool


    Preservation becomes false: tpred tzero has type TBool and evaluates in one step to tzero, which does not have type TBool.
*)

has_type((tpred tzero), tbool).

(*
has_det: has_type(E,T1), has_type(E,T2) => T1 = T2
has_det

Total: 0. s:
Checking depth 1 2Counterexample found:
E = tpred(tzero) 
T1 = tnat 
T2 = tbool 

Checking for counterexamples to 
tc_pres: has_type(M,T), (step(M,M'), gen_tm(M')) => has_type(M',T)
tc_pres
Checking depth 1Counterexample found:
M = tpred(tzero) 
M' = tzero 
T = tbool 


Total: 0. s:

same with NE:


*)
