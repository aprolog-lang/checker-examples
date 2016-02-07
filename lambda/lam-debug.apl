func subst(exp,id,exp) = exp.
subst(u,_,_) = u.

subst(var(Y),Y,N) = N.
subst(var(Y),X,N) = var(Y) :- X # Y.
subst(app(M1,M2),X,N) = app(subst(M1,X,N), subst(M2,X,N)).
subst(lam(M),X,N) = lam(M') :- new y. subst(M@y,X,N)  = M'@y.
subst(pair(M1,M2),X,N) = pair(subst(M1,X,N),subst(M2,X,N)).
subst(fst(M),X,N) = fst(subst(M,X,N)).
subst(snd(M),X,N) = snd(subst(M,X,N)).

pred substp(exp,id,exp,exp).
substp(M,X,N,M') :- subst(M,X,N) = M'.

pred tc (ctx,exp,ty).
tc(G,u,unitTy).
tc([(X,T)|G],var X,T).
tc([(_,_)| G],var X,T) :- tc(G,var(X),T).
tc(G,app(M,N),U) :- tc(G,M,funTy(T,U)), tc(G,N,T).
tc(G,lam(M),funTy(T,U)) :- new x:id. tc([(x,T)|G],M@x,U).
tc(G,pair(M,N),pairTy(T,U)) :- tc(G,M,T), tc(G,N,U).
tc(G,fst(M),T) :- exists U. tc(G,M,pairTy(T,U)).
tc(G,snd(M),U) :- exists T. tc(G,M,pairTy(T,U)).


pred value(exp).
value(u).
value(lam(_)).
value(pair(V1,V2)) :- value(V1),value(V2).


pred step(exp,exp).
step(app(lam(M),N),P) :- value(N), new a.  substp(M@a,a,N,P).
step(fst(pair(M,N)),M):- value(M),value(N).
step(snd(pair(M,N)),N) :- value(M),value(N).
step(app(M1,M2),app(M1',M2)) :- step(M1,M1').
step(app(M1,M2),app(M1,M2')) :- value M1, step(M2,M2').
step(pair(M1,M2),pair(M1',M2)) :- step(M1,M1').
step(pair(M1,M2),pair(M1,M2')) :- value(M1),step(M2,M2').
step(fst(M),fst(M')) :- step(M,M').
step(snd(M),snd(M')) :- step(M,M').

pred steps(exp,exp).
steps(M,M).
steps(M,P) :- step(M,N), steps(N,P).


pred exists_step(exp).
exists_step(app(lam(M),V)):- value V.
exists_step(fst(pair(M,N))) :- value(M),value(N).
exists_step(snd(pair(M,N))) :- value(M),value(N).
exists_step(app(M1,M2)) :- exists_step(M1).
exists_step(app(M1,M2)) :- value(M1),exists_step(M2).
exists_step(pair(M1,M2)) :- exists_step(M1).
exists_step(pair(M1,M2)) :- value(M1),exists_step(M2).
exists_step(fst(M)) :- exists_step(M).
exists_step(snd(M)) :- exists_step(M).


pred progress(exp).
progress(V) :- value(V).
progress(M) :- exists_step(M).


pred valid_ctx(ctx).
valid_ctx([]).
valid_ctx([(X,T)|G]) :- X # G, valid_ctx(G).

