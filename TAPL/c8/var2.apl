(* SF:
Suppose, instead, that we add this new rule to the step relation:
      | ST_Funny1 : ∀t2 t3,
           (tif ttrue t2 t3) ⇒ t3
Which of the above properties become false in the presence of this rule? For each one that does, give a counter-example.

    Determinism becomes false: tif ttrue tzero (tsucc tzero) can now evaluate in one step to either tzero or tsucc tzero.



*)


step((tif ttrue T1 T2),T2).



(*
NF


Checking depth 1Counterexample found:
E = tif(ttrue)(tzero)(tfalse) 
E1 = tzero 
E2 = tfalse 

Total: 0. s:


NE:
Checking depth 1 Counterexample found:
E = tif(ttrue)(tiszero(_201))(tpred(_199)) 
E1 = tiszero(_201) 
E2 = tpred(_199) 
*)
