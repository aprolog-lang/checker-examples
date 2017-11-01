% syntax
exp : type.
id  : name_type.
ty  : type.

u   : exp.
var : id -> exp.
app : (exp,exp) -> exp.
lam : (ty,id\exp) -> exp.
pair: (exp,exp) -> exp.
fst : exp -> exp.
snd : exp -> exp.
let : (id\exp,exp) -> exp.  %% let X=E2 in E1
inl : (exp,ty) -> exp.  %% inl E as T+U
inr : (exp,ty) -> exp.  %% inr E as T+U
case: (exp,id\exp,id\exp) -> exp.  %% case E  of L1 or L2
fix : exp -> exp.

unitTy : ty.
funTy  : (ty,ty) -> ty.
pairTy : (ty,ty) -> ty.
sumTy  : (ty,ty) -> ty.

type ctx = [(id,ty)].

% semantics
func subst(exp,id,exp) = exp.
subst(u,_,_) = u.
subst(var(Y),Y,N) = N.
subst(var(Y),X,N) = var(Y) :- X # Y.
subst(app(M1,M2),X,N) = app(subst(M1,X,N), subst(M2,X,N)).
subst(lam(T,M),X,N) = lam(T,M') :- new y. subst(M@y,X,N)  = M'@y.
subst(pair(M1,M2),X,N) = pair(subst(M1,X,N),subst(M2,X,N)).
subst(fst(M),X,N) = fst(subst(M,X,N)).
subst(snd(M),X,N) = snd(subst(M,X,N)).
subst(let(y\E2,E1),X,N) = let(y\E2',E1') :- y # (E1,N), X # y, subst(E1,X,N) = E1', subst(E2,X,N) = E2'.
subst(inl(E,T),X,N) = inl(subst(E,X,N),T).
subst(inr(E,T),X,N) = inr(subst(E,X,N),T).
subst(case(E,x\L,y\R),X,N) = case(subst(E,X,N),x\L,y\R) :- X # (x,y).
subst(fix(E),X,N) = fix(subst(E,X,N)).

pred substp(exp,id,exp,exp).
substp(M,X,N,M') :- subst(M,X,N) = M'.

pred tc (ctx,exp,ty).
tc(G,u,unitTy).
tc([(X,T)|G],var X,T).
tc([(_,_)| G],var X,T) :- tc(G,var(X),T).
tc(G,app(M,N),U) :- tc(G,M,funTy(T,U)), tc(G,N,T).
tc(G,lam(T,M),funTy(T,U)) :- new x:id. tc([(x,T)|G],M@x,U).
tc(G,pair(M,N),pairTy(T,U)) :- tc(G,M,T), tc(G,N,U).
tc(G,fst(M),T) :- exists U. tc(G,M,pairTy(T,U)).
tc(G,snd(M),U) :- exists T. tc(G,M,pairTy(T,U)).
tc(G,let(x\E2,E1),T) :- exists U. x # G, tc([(x,U)|G],E2,T), tc(G,E1,U).
tc(G,inl(E,sumTy(TL,TR)),sumTy(TL,TR)) :- tc(G,E,TL).
tc(G,inr(E,sumTy(TL,TR)),sumTy(TL,TR)) :- tc(G,E,TR).
tc(G,case(E,x\L,y\R),T) :- x # G, y # G, tc(G,E,sumTy(TL,TR)), tc([(x,TL)|G],L,T), tc([(y,TR)|G],R,T).
tc(G,fix(E),T) :- tc(G,E,funTy(T,T)).


pred value(exp).
value(u).
value(lam(_,_)).
value(pair(V1,V2)) :- value(V1),value(V2).
value(inl(V,T)) :- value(V).
value(inr(V,T)) :- value(V).


pred step(exp,exp).
step(app(lam(T,M),N),P) :- value(N), new a.  substp(M@a,a,N,P).
step(fst(pair(M,N)),M):- value(M),value(N).
step(snd(pair(M,N)),N) :- value(M),value(N).
step(app(M1,M2),app(M1',M2)) :- step(M1,M1').
step(app(M1,M2),app(M1,M2')) :- value M1, step(M2,M2').
step(pair(M1,M2),pair(M1',M2)) :- step(M1,M1').
step(pair(M1,M2),pair(M1,M2')) :- value(M1),step(M2,M2').
step(fst(M),fst(M')) :- step(M,M').
step(snd(M),snd(M')) :- step(M,M').
step(let(x\E2,E1),E) :- value(E1), x # E1, substp(E2,x,E1,E).
step(let(x\E2,E1),let(x\E2,E1')) :- step(E1,E1').
step(inl(E,T), inl(E',T)) :- step(E,E').
step(inr(E,T), inr(E',T)) :- step(E,E').
step(case(inl(V,T),x\L,y\R), E) :- value(V), x # V, substp(L,x,V,E).
step(case(inr(V,T),x\L,y\R), E) :- value(V), y # V, substp(R,y,V,E).
step(fix(lam(T,x\L)),E) :- substp(L,x,fix(lam(T,x\L)),E).
step(fix(E),fix(E')) :- step(E,E').

pred steps(exp,exp).
steps(M,M).
steps(M,P) :- step(M,N), steps(N,P).


pred exists_step(exp).
exists_step(app(lam(T,M),V)):- value V.
exists_step(fst(pair(M,N))) :- value(M),value(N).
exists_step(snd(pair(M,N))) :- value(M),value(N).
exists_step(app(M1,M2)) :- exists_step(M1).
exists_step(app(M1,M2)) :- value(M1),exists_step(M2).
exists_step(pair(M1,M2)) :- exists_step(M1).
exists_step(pair(M1,M2)) :- value(M1),exists_step(M2).
exists_step(fst(M)) :- exists_step(M).
exists_step(snd(M)) :- exists_step(M).
exists_step(let(x\E2,E1)) :- exists_step(E1).
exists_step(let(x\E2,E1)) :- value(E1).
exists_step(inl(E,T)) :- exists_step(E).
exists_step(inr(E,T)) :- exists_step(E).
exists_step(case(E,x\L,y\R)) :- exists_step(E).
exists_step(case(inl(V,T),x\L,y\R)) :- value(V).
exists_step(case(inr(V,T),x\L,y\R)) :- value(V).
exists_step(fix(E)) :- exists_step(E).
exists_step(fix(lam(T,x\L))).


pred progress(exp).
progress(V) :- value(V).
progress(M) :- exists_step(M).


pred valid_ctx(ctx).
valid_ctx([]).
valid_ctx([(X,T)|G]) :- X # G, valid_ctx(G).
