(* SF:
Suppose instead that we remove the rule ST_App1 from the step relation. Which of the following properties of the STLC remain true in the presence of this rule? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample.

    Determinism of step
        Remains true. Removing reduction rules can only make step more deterministic.
    Progress        Becomes false. For example, ((λx:Bool→Bool. λy:Bool→Bool. x) (λz:Bool.z)) (λz:Bool.z) is well typed, but stuck.
    Preservation
        Remains true. Removing reduction rules can't break preservation.
*)


%% we repeat the code here since we *remove* a clause, not add one.
%% so just call var3.apl
%% aprolog -q -v -check-nf  var3.apl check-nf.apl
tm : type.
id  : name_type.
ty  : type.
ctx : type.


type ctx = [(id,ty)]. 

% empty : ctx.
% cons  : (id,ty,ctx) -> ctx.

ttrue : tm.
tfalse : tm.
tif : (tm, tm, tm) -> tm.
var : id -> tm.
app : (tm,tm) -> tm.
lam : id\tm -> tm.

boolTy : ty.
funTy  : (ty,ty) -> ty.

pred value(tm).
value(ttrue).
value(tfalse).
value(lam(_)).

func subst(tm,id,tm) = tm.
subst(ttrue,_,_) = ttrue.
subst(tfalse,_,_) = tfalse.
subst(tif(M1, M2, M3), X,N) = tif(subst(M1,X,N),subst(M2,X,N),subst(M3,X,N)).
subst(var(X),X,N) = N.
subst(var(Y),X,N) = var(Y) :- X # Y.
subst(app(M1,M2),X,N) = app(subst(M1,X,N), subst(M2,X,N)).
subst(lam(M),X,N) = lam(M') :- new y. subst(M@y,X,N)  = M'@y.
% subst(lam(y\M),X,N) = lam(y\subst(M,X,N)) :- y # (X,N).


pred substp(tm,id,tm,tm).
substp(M,X,N,M') :- subst(M,X,N) = M'.

pred step(tm,tm).
% step(app(lam(M),N),P) :- new a:id. exists Y:tm. M = a\Y, substp(Y,a,N,P).
step(app(lam(M),N),P) :- value N,  new a:id. substp(M@a,a,N,P).
%%% step(app(M1,M2),app(M1',M2')) :- step(M1,M1'), M2=M2'. % removed
step(app(M1,M2),app(M1',M2')) :- value(M1),M1=M1',step(M2,M2').
step(tif (ttrue, T1, T2),T1') :- T1 = T1'.
step(tif(tfalse, T1, T2),T2') :- T2 = T2'.
step(tif (T1, T2, T3),tif (T1', T2', T3')):- T2 = T2', T3 = T3', step(T1,T1').


pred exists_step(tm).

exists_step(tif(ttrue,M2,M3)).
exists_step(tif(tfalse,M2,M3)).
exists_step(tif(M1,M2,M3)) :- exists_step(M1).
exists_step(app(lam(M),N)).
%%% exists_step(app(M1,M2)) :- exists_step(M1).
exists_step(app(M1,M2)) :- exists_step(M2).


pred has_type(ctx,tm,ty).
has_type(G,ttrue,boolTy).
has_type(G,tfalse,boolTy).
has_type(G,tif (T1, T2, T3),A):- 
    has_type(G,T1, boolTy), has_type(G,T2,A),has_type(G,T3,A).
has_type([(Y,T)|G],var X,U) :- X = Y,T=U.
has_type([_|G],var X,T) :- has_type(G,var(X),T).
has_type(G,app(M,N),U) :- exists T. has_type(G,M,funTy(T,U)), has_type(G,N,T).
% has_type(G,lam(M),funTy(T,U)) :- new x:id. exists N:tm. M = x\N, has_type([(x,T)|G],N,U).
has_type(G,lam(M),funTy(T,U)) :- new x:id. has_type([(x,T)|G],M@x,U).


pred steps(tm,tm).
steps(M,N) :- M = N.
steps(M,P) :- exists N. step(M,N), steps(N,P).



pred progress(tm).
progress(V) :- value(V).
progress(M) :- exists M'. step(M,M').


pred not_stuck(tm).
not_stuck(V) :- value(V).
not_stuck(M) :- exists_step(M).

pred reduce(tm,tm).
reduce(M,N) :- M = N, value(M).
reduce(M,N) :- exists M'. step(M,M'),reduce(M',N).






(*
progress: has_type([],E,T), (gen_tm(E), gen_ty(T)) => progress(E)
progress
Checking depth 1 2 3 4 5 6 7Counterexample found:
E = app(app(lam(x180257\var(x180257)),lam(x183687\ttrue)),ttrue) 
T = boolTy 

0.358576


*)




pred not_stuck(tm).
not_stuck(V) :- value(V).
not_stuck(M) :- exists_step(M).




 

(* NE

prog 
Total: 8.553096 s:
E = tif(tif(ttrue,ttrue,ttrue),ttrue,ttrue) 
T = boolTy 


May be much better with NE-

*)

(*
NF

E = app(app(lam(x169833\lam(x176386\ttrue)),ttrue),ttrue) 
T = boolTy 
*)
