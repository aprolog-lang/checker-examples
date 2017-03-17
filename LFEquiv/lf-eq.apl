% #use "list.apl".
% #open List.

type tyconst = string.
type const = string.
var : name_type.


kind : type.
ty : type.
obj : type.

ty_k : kind.
pi_k : (ty,var\kind) -> kind.

const_t : tyconst -> ty.
app_t : (ty,obj) -> ty.
pi_t : (ty,var\ty) -> ty.

const_o : const -> obj.
var_o : var -> obj.
app_o : (obj,obj) -> obj.
lam_o : (ty,var\obj) -> obj.

bind : type.
tbind : (tyconst,kind) -> bind.
vbind : (const,ty) -> bind.



%% monomorphic member
pred mem1((obj,var), [(obj,var)]).
	mem1(X,[X|L]).
	mem1(X,[Y|L]) :- mem1(X,L).



(* Generators *)
type ctx_ty = [(var,ty)].
pred kind(kind).
pred ty(ty).
pred obj(obj).
pred wf_ctx(ctx_ty).

kind(ty_k).
kind(pi_k(T,a\K)) :- ty(T),kind(K).

ty(const_t(C)).
ty(app_t(T,M)) :- ty(T),obj(M).
ty(pi_t((T,a\U))) :- ty(T),ty(U).

obj(const_o(C)).
obj(var_o(V)).
obj(app_o(M,N)) :- obj(M),obj(N).
obj(lam_o(T,x\M)) :- ty(T),obj(M).

wf_ctx([]).
wf_ctx([(X,T)|G]) :- X # (T,G), wf_ctx(G).

(* Abstracts away details of global signature *)

pred sig_t(tyconst,kind).
pred sig_o(const,ty).

type subst = [(obj,var)].

func subst_k (kind,subst) = kind.
func subst_t (ty,subst) = ty.
func subst_o (obj,subst) = obj.

subst_k (ty_k,S) = ty_k.
subst_k (pi_k(A,x\K),S) = pi_k(subst_t(A,S),x\subst_k(K,S))
	:- x # S.

subst_t (const_t(C),S) = const_t(C).
subst_t (app_t(A,M),S) = app_t(subst_t(A,S),subst_o(M,S)).
subst_t (pi_t(A,x\B),S) = pi_t(subst_t(A,S),x\subst_t(B,S))
	:- x # S.

subst_o (const_o(C),S) = const_o(C).
subst_o (app_o(M,N),S) = app_o(subst_o(M,S),subst_o(N,S)).
subst_o (lam_o(A,x\M),S) = lam_o(subst_t(A,S),x\subst_o(M,S))
	:- x # S.
subst_o (var_o(X),S) = M :- mem1((M,X),S).


(* Simple kinds and types: page 16 *)

skind : type.
sty : type.

type ctx_sty = [(var,sty)].

ty_sk : skind.
fn_sk : (sty,skind) -> skind.

base_st : tyconst -> sty.
fn_st : (sty,sty) -> sty.

pred sty(sty).
pred skind(skind).
pred wf_sctx(ctx_sty).
skind(ty_sk).
skind(fn_sk(T,K)) :- skind(K), sty(T).

sty(base_st(C)).
sty(fn_st(T,U)) :- sty(T), sty(U).

wf_sctx([]).
wf_sctx([(X,T)|G]) :- X # (T,G), wf_sctx(G).





pred mem2((var, sty), [(var,sty)]).
	mem2(X,[X|L]).
	mem2(X,[Y|L]) :- mem2(X,L).
% ctx_ty

pred mem3((var, ty), [(var,ty)]).
	mem3(X,[X|L]).
	mem3(X,[Y|L]) :- mem3(X,L).

func erase_k (kind) = skind.
func erase_t (ty) = sty.
func erase_ctx (ctx_ty) = ctx_sty.

erase_k (ty_k) = ty_sk.
erase_k (pi_k(A,x\K)) = fn_sk(erase_t(A),erase_k(K)).

erase_t (const_t(C)) = base_st(C).
erase_t (pi_t(A,x\B)) = fn_st(erase_t(A),erase_t(T)).

erase_ctx([]) = [].
erase_ctx([(X,Ty)|G]) = [(X,erase_t(Ty))|erase_ctx(G)].

(* WHR, Algorithmic, and Structural Equality *)

pred whr(obj,obj).
pred alg_eq_o(ctx_sty,obj,obj,sty).
pred str_eq_o(ctx_sty,obj,obj,sty).
pred alg_eq_t(ctx_sty,ty,ty,skind).
pred str_eq_t(ctx_sty,ty,ty,skind).
pred alg_eq_k(ctx_sty,kind,kind).

whr(app_o(M1,M2),app_o(M1',M2)) :- whr(M1,M1').
(* BUG: *)
(* whr(app_o(lam_o(A1,x\M1),M2),subst_o(M2,[(M1,x)])). *)

whr(app_o(lam_o(A1,x\M1),M2),subst_o(M1,[(M2,x)])).

alg_eq_o(D,M,N,A) :- exists M'. whr(M,M'), alg_eq_o(D,M',N,A).
alg_eq_o(D,M,N,A) :- exists N'. whr(N,N'), alg_eq_o(D,M,N',A).
alg_eq_o(D,M,N,fn_st(T1,T2)) :- x # D, 
				alg_eq_o([(x,T1)|D],
					 app_o(M,var_o(x)),
					 app_o(N,var_o(x)),
					 T2).
alg_eq_o(D,M,N,A) :- str_eq_o(D,M,N,A).

str_eq_o(D,var_o(X),var_o(X),T) :- mem2((X,T),D).
str_eq_o(D,const_o(C),const_o(C),erase_t(T)) :- sig_o(C,A).
(* BUG *)
(*str_eq_o(D,app_o(M1,M2),app_o(N1,N2),T1) :-
	str_eq_o(D,M1,M2,fn_st(T2,T1)),
	alg_eq_o(D,N1,N2,T2). *)
str_eq_o(D,app_o(M1,M2),app_o(N1,N2),T1) :-
	str_eq_o(D,M1,N1,fn_st(T2,T1)),
	alg_eq_o(D,M2,N2,T2).


alg_eq_t(D,A,B,fn_sk(T,K)) :- x # D, 
			      alg_eq_t([(x,T)|D],
				       app_t(A,var_o(x)),
				       app_t(B,var_o(x)),
				       K).
alg_eq_t(D,pi_t(A1,x\A2),pi_t(B1,x\B2),ty_sk) :- 
	alg_eq_t(D,A1,B1,ty_sk), 
	x # D, 
	alg_eq_t([(x,erase_t(A1))|D],A2,B2,ty_sk).
alg_eq_t(D,A,B,ty_sk) :- str_eq_t(D,A,B,ty_sk).

str_eq_t(D,const_t(A),const_t(A),erase_k(K)) :- sig_t(A,K).
(* BUG: str_eq_t(D,app_t(A,M),app_t(B,N),K) :-
	str_eq_t(D,A,B,fn_sk(T,K)),
	alg_eq_o(D,M,N,T). *)
str_eq_t(D,app_t(A,M),app_t(A,N),K) :-
	str_eq_t(D,A,B,fn_sk(T,K)),
	alg_eq_o(D,M,N,T).

alg_eq_k(D,ty_k,ty_k).
alg_eq_k(D,pi_k(A,K),pi_k(B,L)) :- alg_eq_t(D,A,B,ty_sk), 
				       x # D, 
				       alg_eq_k([(x,erase_t(A))|D],K@x,L@x).


pred whnf(obj). (* not weak head reducible *)
whnf(var_o(X)).
whnf(app_o(M,N)) :- whnf(M).


(* Type checking algorithm. p. 34. *)

pred tc_o(ctx_ty, obj, ty).
pred tc_t(ctx_ty, ty, kind).
pred tc_k(ctx_ty, kind).

tc_o(G,const_o(C),A) :- sig_o(C,A).
tc_o(G,var_o(X),A) :- mem3((X,A),G).
tc_o(G,app_o(M1,M2),subst_t(A1,[(M2,x)])) :- 
	tc_o(G,M1,pi_t(A2',x\A1)), 
	tc_o(G,M2,A2), 
	alg_eq_t(erase_ctx(G),A2',A2,ty_sk).
tc_o(G,lam_o(A1,x\M2),pi_t(A1,x\A2)) :- 
	tc_t(G,A1,ty_k),
	x # G,
	tc_o([(x,A1)|G],M2,A2).


tc_t(G,const_t(A),K) :- sig_t(A,K).
tc_t(G,app_t(A,M),subst_k(K,[(M,x)])) :- 
	tc_t(G,A,pi_k(B',x\K)), 
	tc_o(G,M,B), 
	alg_eq_t(erase_ctx(G),B',B,ty_sk).
tc_t(G,pi_t(A1,x\A2),ty_k) :- 
	tc_t(G,A1,ty_k),
	x # G,
	tc_t([(x,A1)|G],A2,ty_k).

tc_k(G,ty_k).
tc_k(G,pi_k(A,x\K)) :- tc_t(G,A,ty_k), x # G, tc_k([(x,A)|G],K).

(* Quasi-canonical and atomic objects. p. 36. *)

qc_obj : type.
qa_obj : type.

qa_qc : qa_obj -> qc_obj.
lam_qc : (var\qc_obj) -> qc_obj.
var_qa : var -> qa_obj.
const_qa : const -> qa_obj.
app_qa : (qa_obj,qc_obj) -> qa_obj.

(* Instrumented object equality *)

pred inst_alg_eq(ctx_sty,obj,obj,sty,qc_obj).
pred inst_str_eq(ctx_sty,obj,obj,sty,qa_obj).

inst_alg_eq(D,M,N,A,O) :- whr(M,M'), inst_alg_eq(D,M',N,A,O).
inst_alg_eq(D,M,N,A,O) :- whr(N,N'), inst_alg_eq(D,M,N',A,O).
inst_alg_eq(D,M,N,fn_st(T1,T2),lam_qc(x\O)) :-
	x # D, 
	inst_alg_eq([(x,T1)|D],app_o(M,var_o(x)),app_o(N,var_o(x)),T2,O).
inst_alg_eq(D,M,N,A,qa_qc(O)) :- inst_str_eq(D,M,N,A,O).

inst_str_eq(D,var_o(X),var_o(X),T,var_qa(X)) :- mem2((X,T),D).
inst_str_eq(D,const_o(C),const_o(C),erase_t(A),const_qa(C))
	:- sig_o(C,A).
inst_str_eq(D,app_o(M1,M2),app_o(N1,N2),T1,app_qa(O1,O2)) :-
	inst_str_eq(D,M1,N1,fn_st(T2,T1),O1),
	inst_alg_eq(D,M2,N2,T2,O2).

