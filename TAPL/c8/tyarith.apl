%%  TAPL's typed arithmetic language chap 8
%% AM

tm : type.

ttrue : tm.
tfalse : tm.
tif : tm -> tm -> tm -> tm.
tzero : tm.
tsucc : tm -> tm.
tpred : tm -> tm.
tiszero : tm -> tm.

pred bvalue(tm).

bvalue ttrue.
bvalue tfalse.

pred nvalue(tm).

nvalue tzero.
nvalue (tsucc T) :- nvalue T.

pred value(tm).

value V :- bvalue V ; nvalue V.

pred step (tm,tm).

step((tif ttrue T1 T2),T1).
step((tif tfalse T1 T2),T2).
step((tif T1 T2 T3),(tif T1' T2 T3)):- step(T1,T1').
step((tsucc T),(tsucc T')):- step(T,T').
step((tpred tzero),tzero).
step((tpred (tsucc V)),V') :- V = V', nvalue V .
step((tpred T),(tpred T')):- step(T,T').
step((tiszero tzero),ttrue).
step((tiszero (tsucc V)),tfalse):- nvalue V.
step((tiszero T),(tiszero T')):- step(T,T').

ty : type.

tnat : ty.
tbool: ty.

pred has_type(tm,ty).

has_type(ttrue,tbool).
has_type(tfalse,tbool).
has_type((tif T1 T2 T3),A):- 
    has_type(T1, tbool), has_type(T2,A),has_type(T3,A).
has_type(tzero,tnat).
has_type((tsucc T), tnat):- has_type(T,tnat).
has_type((tpred T), tnat):- has_type(T,tnat).
has_type((tiszero T), tbool):- has_type(T,tnat).

(*
pred progress(tm).
progress(V) :- value(V).
progress(M) :- step(M,M').
*)

%% progress via exists_step
pred exists_step(tm).

exists_step((tif ttrue T1 T2)).
exists_step((tif tfalse T1 T2)).
exists_step((tif T1 T2 T3)):- exists_step(T1).
exists_step((tsucc T)):- exists_step(T).
exists_step((tpred tzero)).
exists_step(tpred (tsucc V)) :- nvalue V.
exists_step((tpred T)):- exists_step(T).
exists_step((tiszero tzero)).
exists_step(tiszero (tsucc V)):- nvalue V.
exists_step((tiszero T)):- exists_step(T).

pred nstuck(tm).
nstuck(V) :- value(V).
nstuck(M) :- exists_step(M).
