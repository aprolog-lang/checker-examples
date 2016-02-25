(* SF:
Suppose, that we add this new rule to the typing relation:
      | T_SuccBool : ∀t,
           ⊢ t ∈ TBool →
           ⊢ tsucc t ∈ TBool

Determinism of step 
		   Remains true 
Progress 
        Becomes false: tsucc ttrue
		       is well typed, but stuck.  Preservation Remains
		       true

*)

has_type((tsucc T),tbool) :- has_type(T,tbool).


(*
Us under NF
aprolog -q -v -check-nf tyarith.apl var1.apl check-nf.apl 


Checking for counterexamples to 
progress: has_type(M,T) => progress(M)
progress
Checking depth 1 2: Counterexample found:
M = tsucc(ttrue) 
T = tbool 

Total: 0.000309 s:

%%%%%%%
Under NE:

neprogress: has_type(M,T), not_nstuck(M) => Prelude.fail
progress
Checking depth 1 2 3 4 5 6 7 8Counterexample found:
M = tif(tsucc(ttrue))(ttrue)(ttrue) 
T = tbool 

does not converge with progress
*)
