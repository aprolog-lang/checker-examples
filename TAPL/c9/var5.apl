(*

Suppose instead that we add the following new rule to the typing relation:
Γ ⊢ t1 ∈ Bool->Bool->Bool 	
Γ ⊢ t2 ∈ Bool 	(T_FunnyApp)  
Γ ⊢ t1 t2 ∈ Bool 	

    Determinism of step
        Remains true. We are only adding to the typing relation, and this can never damage determinism of step.
    Progress
        Remains true. Since the new rule still requires that t1 is a function we can still apply ST_AppAbs to show progress.
    Preservation        Becomes false. For example, ⊢ λx:Bool. λy:Bool. x true ∈ Bool and (λx:Bool. λy:Bool. x) true ⇒ λy:Bool. true but it's not the case that ⊢ λy:Bool. true ∈ Bool

*)

has_type(G,app(E1,E2), boolTy) :- 
	has_type(G,E1,funTy(boolTy,funTy(boolTy,boolTy))), 
        has_type(G,E2,funTy(boolTy,boolTy)).


(*
 det 	3.527766


M = app(lam(x189932\lam(x194954\ttrue)),lam(x195211\ttrue)) 
M' = lam(y195316\ttrue) 
T = boolTy 
Total: 0.157468 s:


*)



(*
NE: 

-
-pres 
    same cex at same dept 6 
    3.42391 s:

*)
