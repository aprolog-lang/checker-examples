(* SF: StlcProp

Suppose instead that we add a new term foo with the following reduction rules:
(λx:A. x) ⇒ foo 
foo ⇒ true 	

Which of the following properties of the STLC remain true in the
presence of this rule? 

    Determinism of step Becomes false. The term (λx:Bool. x) true
    might step to either true by the rule ST_AppAbs or to foo true by
    the rule ST_App1 and ST_Foo1.  

Progress Remains true. We are only
    adding to the step relation, and this can never damage progress.
    Preservation Becomes false. For example, ⊢ λx:Bool.x ∈ Bool→Bool
    and (λx:Bool.x) ⇒ foo by (ST_Foo1), but, since we have no typing
    rules for foo, we cannot prove that ⊢ foo ∈ Bool→Bool.

*)

foo : tm.

subst(foo,_,_) = foo.

step(lam(_),foo).
step(foo,ttrue).

exists_step(lam(_)).
exists_step(foo).



(* NF

step_det
Checking depth 1 2 3 4Counterexample found:
E = app(lam(a13\ttrue),ttrue) 
E1 = ttrue 
E2 = app(foo,ttrue) 

 0.052471 s: 

preservation: has_type(empty,M,T), (step(M,M'), (gen_tm(M'), gen_ty(T))) => has_type(empty,M',T)

M = lam(x911\ttrue) 
M' = foo 
T = funTy(boolTy,boolTy) 
0.000401


*)






(*

NE
Checking depth 1 2 3Counterexample found:
E = app(lam(_19448),tif(ttrue,X20945,T220895)) 
E1 = app(foo,tif(ttrue,X20945,T220895)) 
E2 = app(lam(_19448),X20945) 

0.024806

Checking depth 1 2Counterexample found:
M = lam(x341\ttrue) 
M' = foo 
T = funTy(T334,boolTy) 

0.s

*)
