(*
Bug 6 only applies the hd constant to a partially constructed list (i.e., the term (cons 0) instead of ((cons 0) nil)).
Med
    (term (hd ((cons 1) nil))))
    E = app(c(hd),app(app(c(cons),c(toInt(_N3423675))),c(nil))) 
T = intTy 


*)
func subst(exp,id,exp) = exp.
subst(error,_,_) = error.
subst(c(C) ,_,_) = c(C).
subst(var(X),X,N) = N.
subst(var(Y),X,N) = var(Y) :- X # Y.
subst(app(M1,M2),X,N) = app(subst(M1,X,N), subst(M2,X,N)).
subst(lam((y\M),T),X,N) = lam((y\subst(M,X,N)),T) :- y # (X,N).

pred substp(exp,id,exp,exp).
substp(M,X,N,M') :- subst(M,X,N) = M'.

pred tcc (cnt,ty).
tcc(toInt(_N), intTy).
tcc(nil, listTy).
tcc(hd, funTy(listTy,intTy)).
tcc(tl, funTy(listTy,listTy)).
tcc(cons, funTy(intTy,funTy(listTy,listTy))).
% tcc(plus, funTy(intTy,funTy(intTy,intTy))).


pred tc (ctx,exp,ty).
tc(_,error,T).
tc(_,c(C),T) :- tcc(C,T).
tc([(X,T)|G],var X,T).
tc([_|G],var X,T) :- tc(G,var(X),T).
tc(G,app(M,N),U) :- exists T. tc(G,M,funTy(T,U)), tc(G,N,T).
tc(G,lam(M,T),funTy(T,U)) :- new x:id.  tc([(x,T)|G],M@x,U).


pred valid_ctx(ctx).
valid_ctx([]).
valid_ctx([(X,T)|G]) :- X # G, valid_ctx(G).


pred value(exp).
value(c(_)).
% value(error).
value(lam(_,_)).
value(app(c(cons),V)) :- value(V).
value(app(app(c(cons),V1),V2)) :- value(V1),value(V2).

pred step(exp,exp).
step(app(c(hd),(app(c(cons),X))),X) :- value X. %%% BUG
%%step(app(c(hd), c (nil)),error).
%% step(app(c(tl), c (nil)),error).
step(app(c(tl),app(app(c(cons),V),VS)),VS) :- value(V),value(VS).
%%% step(app(c(tl),app(c(cons),app(_,XS))),XS).
%% step(app(error,error),error).
%% step(app(_,error),error).
step(app(lam(M,_),N),P) :- value(N), new a.  substp(M@a,a,N,P).
step(app(M1,M2),app(M1',M2')) :- step(M1,M1'), M2=M2'.
step(app(M1,M2),app(M1',M2')) :- value M1,  M1=M1', step(M2,M2').


pred exists_step(exp).
% exists_step(M) :- exists M'. step(M,M').

% exists_step(app(lam(_),_)).
exists_step(app(lam(M,T),V)):- value V.
exists_step(app(c(hd),(app(c(cons),X)))) :- value X. % bug
exists_step(app(c(tl),app(app(c(cons),V),VS))) :- value(V),value(VS).
exists_step(app(M1,M2)) :- exists_step(M1).
exists_step(app(M1,M2)) :- value M1, exists_step(M2).


pred is_err(exp).
is_err(app(c(hd), c (nil))).
is_err(app(c(tl), c (nil))).
is_err(error).
is_err(app(E1,E2)) :- is_err(E1).
is_err(app(V1,E2)) :- value(V1),is_err(E2).

pred progress(exp).
progress(V) :- value(V).
progress(E) :- is_err(E).
progress(M) :- exists_step(M).

(*
#check "tc_pres" 11 : 
  tc([],M,T), step(M,M'), 
  gen_exp(M),gen_exp(M'),gen_ty(T) => tc([],M',T).



#check "foo" 20 : 
M = app(c(hd),app(app(c(cons),c(toInt(0))),c(nil))) ,
not_exists_step(M) => fail.
*)
