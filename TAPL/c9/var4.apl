(*
Suppose instead that we add the following new rule to the reduction relation:
   	(ST_FunnyIfTrue)  
(if true then t1 else t2) ⇒ true 	

    Determinism of step
        Becomes false, for instance: (if true then false else false) ⇒ false and (if true then false else false) ⇒ true
    Progress
        Remains true. We are only adding to the step relation, and this can never damage progress.
    Preservation        Becomes false. For example, ⊢ if true then (λx:Bool.x) else (λx:Bool.x) ∈ Bool→Bool and (if true then (λx:Bool.x) else (λx:Bool.x)) ⇒ true but it's not the case that ⊢ true ∈ Bool → Bool.

*)

step(tif(ttrue,_,_),ttrue).



(*

step_detv4

E = tif(ttrue,var(X158),T235) 
E1 = var(X158) 
E2 = ttrue 
Running	0.000366


preservation
Checking depth 1 2 3 4 5 6Counterexample found:
M = tif(ttrue,lam(x5594\ttrue),lam(x5839\ttrue)) 
M' = ttrue 
T = funTy(funTy(boolTy,boolTy),boolTy) 

0.0332

*)


(*

nestep_det

E = tif(ttrue,lam(_250),T235) 
E1 = lam(_250) 
E2 = ttrue 

0.000173


ne_tc_pres
Checking depth 1 2 3 4 5 6Counterexample found:
M = tif(ttrue,lam(x14840\ttrue),lam(x15085\ttrue)) 
M' = ttrue 
T = funTy(T14833,boolTy) 

Total: 0.181903 s:

Note that this is the same cex of NF but non-ground in T


*)
