func subst(exp,id,exp) = exp.

subst(var(Y),X,N) = N :- X = Y.
subst(var(Y),X,N) = var(X') :- X # Y, X = X'.
subst(app(M1,M2),X,N) = app(subst(M1,X,N), subst(M2,X,N)).
subst(lam(M),X,N) = lam(M') :- new y. subst(M@y,X,N)  = M'@y.
subst(u,_,_) = u.
subst(pair(M1,M2),X,N) = pair(subst(M1,X,N),subst(M1,X,N)).
subst(fst(M),X,N) = fst(subst(M,X,M)).
subst(fst(M),X,N) = snd(subst(M,X,N)).


pred substp(exp,id,exp,exp).
substp(M,X,N,M') :- subst(M,X,N) = M'.


pred valid_ctx(ctx).
valid_ctx([]).
valid_ctx([(X,T)|G]) :- X # G, valid_ctx(G).

pred tc (ctx,exp,ty).
tc([(Y,T)|G],var X,U) :- X = Y,T=U.
tc(G,lam(M),funTy(T,U)) :- new x:id. tc([(x,T)|G],M@x,U).
% tc(G,lam(M),funTy(T,U)) :- new x:id. exists N:exp. M = x\N, tc(cons(x,T,G),N,U).
% tc(G,lam(x\M),funTy(T,U)) :- x#G, tc(cons(x,T,G),M,U).
tc(G,app(M,N),U) :- exists T. tc(G,M,funTy(U,T)), tc(G,N,T).
tc(G,pair(M,N),pairTy(T,U)) :- tc(G,M,T), tc(G,N,U).
tc(G,fst(M),T) :- exists U. exists N. tc(G,N,pairTy(T,U)). %% OK this exists N is funky, but it would be inserted by the front end
tc(G,snd(M),T) :- exists U. tc(G,M,pairTy(T,U)).
tc(G,u,unitTy).

pred value(exp).
value(lam(_)).
value(u).
value(pair(V1,V2)) :- value(V1),value(V2).

pred step(exp,exp).
step(app(lam(M),N),P) :- value(N), new a.  substp(P,a,N,M@a).
step(fst(pair(M,N)),M):- value(M),value(N).
step(snd(pair(M,N)),N) :- value(M),value(N).
step(app(M1,M2),app(M1',M2)) :- step(M1,M1').
step(app(M1,M2),app(M1,M2')) :-value(M1), step(M2,M2').
step(pair(M1,M2),pair(M1',M2)) :- step(M1,M1').
step(pair(M1,M2),pair(M1,M2')) :- value(M1),step(M2,M2').
step(fst(M),fst(M')) :- step(M,M').
step(snd(M),snd(M')) :- step(M,M').
% step(snd(pair(M,N)),M) :- value(M).

pred steps(exp,exp).
steps(M,N) :- M = N.
steps(M,P) :- exists N. step(M,N), steps(N,P).

pred reduce(exp,exp).
reduce(M,N) :- M = N.
reduce(M,N) :- exists M'. step(M,M'),reduce(M',N).

pred exists_step(exp).
%exists_step(app(lam(M),N)).
exists_step(app(lam(M),V)):- value V.
exists_step(fst(pair(M,N))).
exists_step(snd(pair(M,N))).
exists_step(app(M1,M2)) :- exists_step(M1).
exists_step(app(M1,M2)) :- value(M1),exists_step(M2).
exists_step(pair(M1,M2)) :- exists_step(M1).
exists_step(pair(M1,M2)) :- value(M1),exists_step(M2).
exists_step(fst(M)) :- exists_step(M).
exists_step(snd(M)) :- exists_step(M).


pred progress(exp).
progress(V) :- value(V).
progress(M) :- exists_step(M).


