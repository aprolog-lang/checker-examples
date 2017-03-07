
(*
BUG1
The first confuses the range and domain types of the function in the application rule, and has the small counterexample: (hd 0).
Shallow, size 3  (hd 0)))

app rule the range of the function is matched to the argument
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


func tccf (cnt) = ty.
tccf(toInt(_N)) =  intTy.
tccf(nil) =  listTy.
tccf(hd) =  funTy(listTy,intTy).
tccf(tl) =  funTy(listTy,listTy).
tccf(cons) =  funTy(intTy,funTy(listTy,listTy)).

pred tcc (cnt,ty).
tcc(toInt(_N), intTy).
tcc(nil, listTy).
tcc(hd, funTy(listTy,intTy)).
tcc(tl, funTy(listTy,listTy)).
tcc(cons, funTy(intTy,funTy(listTy,listTy))).
% tcc(plus, funTy(intTy,funTy(intTy,intTy))).


pred tc (ctx,exp,ty).
tc(_,error,T).
tc(_,c(C),T) :- tccf(C) = T.
tc([(Y,T)|G],var X,U) :- X = Y,T=U.
tc([_|G],var X,T) :- tc(G,var(X),T).
tc(G,app(M,N),U) :- exists T. tc(G,M,funTy(T,U)), tc(G,N,U). %%% here T := U
tc(G,lam(M,T),funTy(T_,U)) :- (new x:id.  tc([(x,T)|G],M@x,U),T=T_).


pred valid_ctx(ctx).
valid_ctx([]).
valid_ctx([(X,T)|G]) :- X # G, valid_ctx(G).


pred value(exp).
value(c(_)).
value(lam(_,_)).
value(app(c(cons),V)) :- value(V).
value(app(app(c(cons),V1),V2)) :- value(V1),value(V2).

pred step(exp,exp).
step(app(c(hd),app(app(c(cons),V),VS)),V) :- value(V),value(VS).
step(app(c(tl),app(app(c(cons),V),VS)),VS) :- value(V),value(VS).
step(app(lam(M,_),N),P) :- value(N), new a.  substp(M@a,a,N,P).
step(app(M1,M2),app(M1',M2')) :- step(M1,M1'), M2=M2'.
step(app(M1,M2),app(M1',M2')) :- value M1,  M1=M1', step(M2,M2').


pred exists_step(exp).
%exists_step(app(lam(_),_)).
exists_step(app(lam(M,T),V)):- value V.
exists_step(app(c(hd),app(app(c(cons),V),VS))) :- value(V),value(VS).
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


(*NE: 
pres

Total: 2.180536 s:
M = app(lam(x2774962\app(var(x2774962),error),funTy(T2925599,intTy)),c(toInt(_N3114621))) 
M' = app(c(toInt(_N3114621)),error) 
T = intTy 

progress fails

Total: 4.9258 s:
E = app(c(hd),c(toInt(_N1653371))) 
T = intTy 

hd(1)
*)

(* NF

pres
M = app(lam(x\app(var(x),error),funTy(T,intTy)),c(toInt(N))) 
M' = app(c(toInt(N)),error) 
T = intTy 
a236018 # N
a236018 # N
x # T


prog
E = app(c(hd),c(toInt(_N1611))) 
T = intTy 

samebug
*)

