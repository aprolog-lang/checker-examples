(* SF:

Suppose we add the following new rule to the typing relation of the STLC:
   	(T_FunnyAbs)  
⊢ λx:Bool.t ∈ Bool 	
Which of the following properties of the STLC remain true in the presence of this rule? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample.

    Determinism of step
        Remains true. We're not changing the step relation.
    Progress
        Becomes false. For instance if (λx:Bool.false) then false else false is a term that would become typable, although it is stuck.
    Preservation
        Remains true. λx:Bool.t doesn't step.


*)

has_type(G,lam(_),boolTy).

(*
NF
progress
Checking depth 1 2 3 4 5Counterexample found:
E = tif(lam(a12430\var(X12806)),ttrue,ttrue) 
       T = boolTy

	       NE same
*)
