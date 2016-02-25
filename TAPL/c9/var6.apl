(* SF

Suppose instead that we add the following new rule to the typing relation:
Γ ⊢ t1 ∈ Bool 	
Γ ⊢ t2 ∈ Bool 	(T_FunnyApp')  
Γ ⊢ t1 t2 ∈ Bool 	

    Determinism of step
        Remains true. We are not changing the step relation.
    Progress
        Becomes false. For instance, true true is a term that becomes typable (at type Bool), but which is stuck.
    Preservation
        Remains true. There are 3 ways t1 t2 can reduce. For ST_App1 and ST_App2 we can still apply the induction hypothesis. In order to reduce t1 t2 using ST_AppAbs t1 would need to be a function, but functions don't have type Bool.

*)

has_type(G,app(E1,E2),boolTy) :- has_type(G,E1,boolTy),has_type(G,E2,boolTy).

(*
progress: has_type(empty,E,T)) => progress(E)
progress
Checking depth 1 2 3
E = app(ttrue,ttrue) 
T = boolTy 
: 0.004805 s:

*)


(*

- det at 6 > 20

- pres at 7 > 20

same cex at dep 6. 
Total: 0.172908 s:

*)

