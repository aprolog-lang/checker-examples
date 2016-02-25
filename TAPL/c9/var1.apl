(*
Suppose we add a new term zap with the following reduction rule:
   	(ST_Zap)  
t ⇒ zap 	
and the following typing rule:
   	(T_Zap)  
Γ ⊢ zap : T 	
Which of the following properties of the STLC remain true in the presence of this rule? 

    Determinism of step
        Becomes false. For instance (if true then false else true) ⇒ false and (if true then false else true) ⇒ zap.
    Progress
        Remains true. zap can have any type.
    Preservation
        Remains true. Every term (including zap) can take a step to zap.
*)

zap : tm.

subst(zap,_,_) = zap.

step(_,zap).

has_type(_,zap,_).

exists_step(zap).


(*
NF: 
E = tif(ttrue,var(X162),T220) 
E1 = var(X162) 
E2 = zap 
*)

(* NE 

- det

E = tif(ttrue,lam(_241),T235) 
E1 = lam(_241) 
E2 = zap 
Running took 0. s

*)
