(* Lambda zap: Walker et al. ICFP 2006 *)

    
color : type.
r : color.
g : color.
b : color.

opt_color : type.

none : opt_color.
some : color -> opt_color.



pred color(color).
color(r).
color(g).
color(b).

ty : type.
cty : type.

intTy : ty.
boolTy : ty.
arrTy : (cty,cty) -> ty.

c : (color,ty) -> cty.
rgb : (ty) -> cty.


loc : name_type.
value : type.
vl : loc -> value.
vn : int -> value.
vb : bool -> value.



pred value(value).
value(vl(L)).
value(vn(N)).
value(vb(B)).

type cvalue = (color,value).
pred cvalue(cvalue).
cvalue(C,V) :- color(C), value(V).

id : name_type.
exp : type.


var : id -> exp.
val : cvalue -> exp.
plus : (exp,exp) -> exp.
leq : (exp,exp) -> exp.
cond : (exp,exp,exp) -> exp.
lam3 : (ty,id\id\id\exp) -> exp.
app : (exp,exp) -> exp.
tri : (exp,exp,exp) -> exp.
let3 : (exp,id\id\id\exp) -> exp.
let : (exp,id\exp) -> exp.
out : (exp,exp) -> exp.

type ctx = [(id,cty)].
type lctx = [(loc,ty)].
type heap = [(loc,exp)].
type state = ([(loc,exp)],exp).

pred append([int],[int],[int]).
	append([],L,L).
	append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).

func vote(cvalue,cvalue,cvalue) = value.
vote((_,V),(_,V),_) = V.
vote((_,V),_,(_,V)) = V.
vote(_,(_,V),(_,V)) = V.


func subst(exp,exp,id) = exp.
subst(var(X),M,X) = M.
subst(var(Y),M,X) = var(Y) :- X # Y.
subst(val(V),_,_) = val(V).
subst(plus(E1,E2),M,X) = plus(subst(E1,M,X),subst(E2,M,X)).
subst(leq(E1,E2),M,X) = leq(subst(E1,M,X),subst(E2,M,X)).
subst(cond(E,E1,E2),M,X) = cond(subst(E,M,X),subst(E1,M,X),subst(E2,M,X)).
subst(app(E1,E2),M,X) = app(subst(E1,M,X),subst(E2,M,X)).
subst(out(E1,E2),M,X) = out(subst(E1,M,X),subst(E2,M,X)).
subst(tri(E,E1,E2),M,X) = tri(subst(E,M,X),subst(E1,M,X),subst(E2,M,X)).
subst(lam3(T,x1\x2\x3\E),M,X) = lam3(T,x1\x2\x3\subst(E,M,X))
	:- x1 # (M,X), x2 # (M,X), x3 # (M,X).
subst(let3(E,x1\x2\x3\E'),M,X) = let3(subst(E,M,X),x1\x2\x3\subst(E',M,X))
	:- x1 # (M,X), x2 # (M,X), x3 # (M,X).
subst(let(E,x\E'),M,X) = let(subst(E,M,X),x\subst(E',M,X))
	:- x # (M,X).

func subst3(exp,exp,id,exp,id,exp,id) = exp.
subst3(E,E1,X1,E2,X2,E3,X3) = subst(subst(subst(E,E1,X1),E2,X2),E3,X3).

%% monomorphic member
pred mem1((id,color,ty),[(id,color,ty)]).
	mem1(X,[X|L]).
	mem1(X,[Y|L]) :- mem1(X,L).

pred mem2((loc,exp),[(loc,exp)]).
	mem2(X,[X|L]).
	mem2(X,[Y|L]) :- mem2(X,L).


pred mem3((loc,ty),[(loc,ty)]).
	mem3(X,[X|L]).
	mem3(X,[Y|L]) :- mem3(X,L).

(* Symbolic operational semantics *)
(* Evaluation context step *)
pred step(state,[int],state).
(* Redex step *)
pred step1(state,[int],state).

step(E,S,E') :- step1(E,S,E').
step((M,plus(E1,E2)),S,(M',plus(E1',E2))) :- step((M,E1),S,(M',E1')).

(* BUG *)
(*step((M,plus(val(V1),E2)),S,(M',plus(val(V1),E2'))) :- step((M,E2),S,(M,E2')).*)
step((M,plus(val(V1),E2)),S,(M',plus(val(V1),E2'))) :- step((M,E2),S,(M',E2')).
step((M,leq(E1,E2)),S,(M',leq(E1',E2))) :- step((M,E1),S,(M',E1')).
(* BUG *)
(*step((M,leq(val(V1),E2)),S,(M',leq(val(V1),E2'))) :- step((M,E2),S,(M,E2')).*)
step((M,leq(val(V1),E2)),S,(M',leq(val(V1),E2'))) :- step((M,E2),S,(M',E2')).
(* BUG *)
(*step((M,cond(E,E1,E2)),S,(M',cond(E',E1,E2))) :- step((M,E1),S,(M',E1')).*)
step((M,cond(E,E1,E2)),S,(M',cond(E',E1,E2))) :- step((M,E),S,(M',E')).
step((M,app(E1,E2)),S,(M',app(E1',E2))) :- step((M,E1),S,(M',E1')).
step((M,app(tri(val(V1),val(V2),val(V3)),E)),S,
	(M',app(tri(val(V1),val(V2),val(V3)),E'))) 
	:- step((M,E),S,(M',E')).
step((M,tri(E1,E2,E3)),S,(M',tri(E1',E2,E3))) 
	:- step((M,E1),S,(M',E1')).
step((M,tri(val(V1),E2,E3)),S,(M',tri(val(V1),E2',E3))) 
	:- step((M,E2),S,(M',E2')).
step((M,tri(val(V1),val(V2),E3)),S,(M',tri(val(V1),val(V2),E3'))) 
	:- step((M,E3),S,(M',E3')).
step((M,let3(E1,E2)),S,(M',let3(E1',E2))) :- step((M,E1),S,(M',E1')).
step((M,let(E1,E2)),S,(M',let(E1',E2))) :- step((M,E1),S,(M',E1')).


step1((M,plus(val (C,_),val (C,_))),[],(M,val (C,vn _))).
step1((M,leq(val(C,_), val(C,_))), [], (M, val(C,vb _))).
step1((M,cond(val(_,vb true), E1, E2)), [], (M,E1)).
step1((M,cond(val(_,vb false), E1, E2)), [], (M,E1)).
step1((M,lam3(T,x1\x2\x3\E)), [], ([(L,lam3(T,x1\x2\x3\E))|M],tri(val(r,vl(L)),val(g,vl(L)),val(b,vl(l)))))
	:- L # M.
step1((M,app(tri(val V1,val V2,val V3), tri(val W1,val W2,val W3))),[],
      (M,N))
	:- vote(V1,V2,V3) = vl(L), 
	mem2((L,lam3(T,x1\x2\x3\E)),M),
	N = subst3(E,val W1,x1,val W2,x2,val W3,x3).
step1((M,let(val V,x\E)),[],(M,N)) :- N = subst(E,val V, x).
step1((M,let3(tri(val V1, val V2, val V3),x1\x2\x3\E)),[],
	(M,N)) :- N= subst3(E,val V1,x1,val V2,x2,val V3,x3).
step1((M,out(tri(val V1, val V2, val V3),E2)),[N],(M,E2))
	:- vote(V1,V2,V3) = vn N.

pred steps(state,[int],state).
steps((M,E),[],(M,E)).
steps((M1,E1),S,(M3,E3)) 
	:- step((M1,E1),S1,(M2,E2)), 
	steps((M2,E2),S2,(M3,E3)),
	append(S1,S1,S).

pred fault(exp,exp).
fault(val(C,W),val(C,W')).
fault(plus(E1,E2), plus(E1',E2)) :- fault(E1,E1').
fault(plus(E1,E2), plus(E1,E2')) :- fault(E2,E2').
fault(leq(E1,E2), leq(E1',E2)) :- fault(E1,E1').
fault(leq(E1,E2), leq(E1,E2')) :- fault(E2,E2').
fault(cond(E1,E2,E3),cond(E1',E2,E3)) :- fault(E1,E1').
fault(cond(E1,E2,E3),cond(E1,E2',E3)) :- fault(E2,E2').
fault(cond(E1,E2,E3),cond(E1,E2,E3')) :- fault(E3,E3').
fault(app(E1,E2), app(E1',E2)) :- fault(E1,E1').
fault(app(E1,E2), app(E1,E2')) :- fault(E2,E2').
fault(tri(E1,E2,E3),tri(E1',E2,E3)) :- fault(E1,E1').
fault(tri(E1,E2,E3),tri(E1,E2',E3)) :- fault(E2,E2').
fault(tri(E1,E2,E3),tri(E1,E2,E3')) :- fault(E3,E3').
fault(lam3(T,x1\x2\x3\E),lam3(T,x1\x2\x3\E')) :- fault(E,E').
fault(let3(E1,x1\x2\x3\E2),let3(E1',x1\x2\x3\E2)) :- fault(E1,E1').
fault(let3(E1,x1\x2\x3\E2),let3(E1,x1\x2\x3\E2')) :- fault(E2,E2').
fault(let(E1,x\E2),let(E1',x\E2)) :- fault(E1,E1').
fault(let(E1,x\E2),let(E1,x\E2')) :- fault(E2,E2').

pred fsteps(state,state).
fsteps(S1,S2) :- steps(S1,S,S2).
fsteps(S1,S2) 
	:- steps(S1,_,(M,E)), 
	fault(E,E'), 
	steps((M,E'),_,S2).

pred fsteps2(state,state).
fsteps2((M1,E1),(M3',E3')) 
	:- steps((M1,E1),_,(M1',E1')),
	fault(E1',E2),
	steps((M1',E2),_,(M2',E2')),
	fault(E2',E3),
	steps((M2',E3),_,(M3',E3'))
	.



pred tc([(id,color,ty)],[(loc,ty)],opt_color, exp, cty).
tc(G,D,some(C),val(C,W),c(C,I)).
tc(G,D,Z,val(C,vn(N)),c(C,intTy)).
tc(G,D,Z,val(C,vb(N)),c(C,boolTy)).
tc(G,D,Z,var(X),c(C,I)) :- mem1((X,C,I),G).
tc(G,D,Z,val(C,vl(L)),c(C,I)) :- mem3((L,I),D).
tc(G,D,Z,plus(E1,E2),c(C,intTy)) 
	:- tc(G,D,Z,E1,c(C,intTy)),
	tc(G,D,Z,E2,c(C,intTy)). 
tc(G,D,Z,leq(E1,E2),c(C,boolTy)) 
	:- tc(G,D,Z,E1,c(C,intTy)),
	tc(G,D,Z,E2,c(C,intTy)). 
tc(G,D,Z,cond(E,E1,E2),T)
	:- tc(G,D,Z,E,rgb(boolTy)),
	tc(G,D,Z,E1,T),
	tc(G,D,Z,E2,T).
tc(G,D,Z,lam3(I,E),rgb(arrTy(rgb(I),T2)))
	:- new x1,x2,x3.
	tc([(x1,r,I),(x2,g,I),(x3,b,I)|G],D,Z,E@x1@x2@x3,T2).
tc(G,D,Z,app(E1,E2),T2)
	:- tc(G,D,Z,E1,rgb(arrTy(T1,T2))),
	tc(G,D,Z,E2,T1).
tc(G,D,Z,tri(E1,E2,E3),rgb(I))
	:- tc(G,D,Z,E1,c(r,I)),
	tc(G,D,Z,E2,c(g,I)),
	tc(G,D,Z,E3,c(b,I)).
tc(G,D,Z,let(E1,x\E2),T2)
	:- tc(G,D,Z,E1,c(C,I)),
	tc([(x,C,I)|G],D,Z,E2,T2).
tc(G,D,Z,let3(E1,x1\x2\x3\E2),T2)
	:- tc(G,D,Z,E1,rgb(I)),
	tc([(x1,r,I),(x2,g,I),(x3,b,I)|G],D,Z,E2,T2).

pred heaptc(opt_color,[(loc,exp)],[(loc,ty)]).
heaptc(Z,[],[]).
heaptc(Z,[(A,lam3(I,x1\x2\x3\E2))|M],[(A,arrTy(rgb(I),T))|D])
	:- tc([(x1,r,I),(x2,g,I),(x3,b,I)],D,(Z),E2,T),
	heaptc(Z,M,L).

pred statetc(opt_color, state, cty).
statetc(Z,(M,E),T) :- heaptc(Z,M,D), tc([],D,(Z),E,T).

pred exists_c_statetc(state,cty).
exists_c_statetc((M,E),T) :- exists C. statetc(some(C), (M,E), T).

(* Definition 1 *)
pred safe2(state).
safe2(M,val(_)).
safe2(M,tri(val(_),val(_),val(_))).
safe2(M,E) :- step((M,E),S,(M',E')).
(* TODO: Safety for states with vote2 undefined. *)




pred ctx(ctx).
ctx([]).
ctx([(X,T)|G]) :- X # G,  ctx(G).

pred lctx(lctx).
lctx([]).
lctx([(X,T)|G]) :- X # G, lctx(G).

pred heap(heap).
heap([]).
heap([(X,E)|G]) :- X # G, heap(G).

pred state(state).
state(M,E) :- heap(M).


