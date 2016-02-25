tm : type.
id  : name_type.
ty  : type.
% ctx : type.

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

%% not left linearized as it is a function
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
step(app(lam(M),N),P) :- value N,  new a:id. substp(M@a,a,N,P).
step(app(M1,M2),app(M1',M2')) :- step(M1,M1'), M2=M2'.
step(app(M1,M2),app(M1',M2')) :- value(M1),M1=M1',step(M2,M2').
step(tif(ttrue, T1, T2),T1') :- T1 = T1'.
step(tif(tfalse, T1, T2),T2') :- T2 = T2'.
step(tif (T1, T2, T3),tif (T1', T2', T3')):- T2 = T2', T3 = T3', step(T1,T1').


pred exists_step(tm).

exists_step(tif(ttrue,M2,M3)).
exists_step(tif(tfalse,M2,M3)).
exists_step(tif(M1,M2,M3)) :- exists_step(M1).
exists_step(app(lam(M),N)).
exists_step(app(M1,M2)) :- exists_step(M1).
exists_step(app(M1,M2)) :- exists_step(M2).


pred has_type(ctx,tm,ty).
has_type(G,ttrue,boolTy).
has_type(G,tfalse,boolTy).
has_type(G,tif (T1, T2, T3),A):- 
    has_type(G,T1, boolTy), has_type(G,T2,A),has_type(G,T3,A).
%  has_type(cons(Y,T,G),var X,U) :- X = Y,T=U.
% has_type(cons(_,_,G),var X,T) :- has_type(G,var(X),T).
has_type([(Y,T)|G],var X,U) :- X = Y,T=U.
has_type([(Y,_)|G],var X,T) :- X # Y, has_type(G,var(X),T).

has_type(G,app(M,N),U) :- exists T. has_type(G,M,funTy(T,U)), has_type(G,N,T).
has_type(G,lam(M),funTy(T,U)) :- new x:id. has_type([(x, T) |G],M@x,U).


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





