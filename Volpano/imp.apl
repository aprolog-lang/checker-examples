%% Author: AM
%% First we introduce IMP (a la Nipkow)

%% we cannot use int,bool from Prelude, so we deploy ours
%% all relational

nat : type.
z : nat.
sc : nat -> nat.

pred add (nat,nat,nat).
add(z,M, N) :- N = M.
add(sc(N),M ,sc K) :- add(N,M,K).

pred le (nat,nat).
le(z,_).
le(sc(L1),sc(L2)) :- le (L1,L2).

pred gt (nat,nat).
gt(sc(_),z).
gt(sc(X),sc(Y)) :- gt(X,Y).

% strictly less
pred ll (nat,nat).
ll(z,sc(_)).
ll(sc(L1),sc(L2)) :- ll (L1,L2).

mbool: type.
mtrue: mbool.
mfalse : mbool.

func llf  (nat,nat) = mbool.
(*
llf(N,M) = mtrue :- ll(N,M).
llf(N,M) = mfalse :- le(M,N).
*)
% removed if-then-else because ne-simpl lacks support for it
% llf(N,M) = B :- (ll(N,M) -> B = mtrue | B = mfalse).
llf(N,M) = mtrue :- ll(N,M), !.
llf(N,M) = mfalse.


% llf(sc(_),z) = mfalse.
% llf(sc(L1),sc(L2)) = llf (L1,L2).


% aexp
id: name_type.
aexp : type.

c : nat -> aexp.
var : id -> aexp.
plus : (aexp,aexp) -> aexp.

% the state
type state = [(id,nat)].

% evaluate aexp
pred aval(aexp,state,nat).
aval(c(N),S, M) :- N = M.
aval(var X,[(Y,N) |_],M) :- X = Y, M = N.
aval(var X,[(Y,_) |St],N) :-  X # Y, aval(var(X),St,N).
aval(plus(A1,A2),St,N) :- 
   exists N1. aval(A1,St,N1),
   exists N2. aval(A2,St,N2), 
   add(N1,N2,N).


% bexp 
bexp : type.

b : mbool -> bexp .
less : (aexp, aexp) -> bexp.
cnot : bexp -> bexp.
cand : (bexp,bexp) -> bexp.

% can't use 'not' which is NF
func hnot(mbool) = mbool.
hnot(mtrue) = mfalse.
hnot(mfalse) = mtrue.

func hand(mbool,mbool) = mbool.
hand(mtrue,mtrue) = mtrue.
hand(mfalse,_) = mfalse.
hand(_,mfalse) = mfalse.

pred bval(bexp,state,mbool).
bval(b(B),S, B') :- B = B'.
bval(cnot(B),S,BN) :- 
   exists Vb. bval(B,S,Vb), 
   BN = hnot Vb.
bval(cand(B1,B2),S, BA) :-  
   exists V1. bval(B1,S,V1), 
   exists V2. bval(B2,S,V2), 
   BA = hand(V1,V2).
bval(less(A1,A2),S, BL) :- 
   exists V1. aval(A1,S,V1), 
   exists V2. aval(A2,S,V2), 
   BL = llf(V1,V2).


% commands
cmd : type.
skip : cmd.
assn : (id , aexp) -> cmd.
seq : (cmd , cmd) -> cmd. 
ift : (bexp,cmd,cmd) -> cmd.
whi : (bexp,cmd) -> cmd.

pred upd(state,id,nat,state).
upd([],X,N, [(X',N')]) :- X = X',N = N'.
upd([(X,_)|St],X',N, UpSt) :- X = X', UpSt = [(X,N)|St]. 
upd([(X,Nx)|St],Y,N,[(X',Nx')|St']):- X # Y, X = X', Nx = Nx', upd(St,Y,N,St').


pred eval  (state,cmd,state).
eval(S,skip,S') :- S = S'.

eval(S,assn(X,A), S') :-  exists Va. aval(A,S,Va), upd(S,X,Va,S').

eval(S1,seq(C1,C2),S3) :- exists S2. eval(S1,C1,S2),eval(S2,C2,S3).

eval(S,ift(B,C1,C2),S')  :- 
  exists Res. bval(B,S, Res),
  (Res = mtrue -> eval(S,C1,S') | eval(S,C1,S')).

eval(S1,whi(B,C),S2) :-
   exists Res. bval(B,S1, Res), 
   (Res = mfalse -> S1 = S2 | 
   exists S'. eval(S1,C,S'),eval(S',whi(B,C),S2)).


(* before guards:
eval(S,ift(B,C1,C2),S')  :- bval(B,S, mtrue),eval(S,C1,S').
eval(S,ift(B,C1,C2),S')  :- bval(B,S, mfalse),eval(S,C2,S').

eval(S1,whi(B,C),S3) :- bval(B,S,mtrue), exists S2. eval(S1,C,S2),eval(S2,whi(B,C),S3).
eval(S,whi(B,C),S') :- bval(B,S, mfalse), S = S'. 
*)

%aval(plus(c(sc z),c (sc z)),[],N).
% bval(cand(b mtrue, b mtrue), [], B).
% eval([],assn(x, c z),SS).
% eval( [(y,z)],assn(x, var y),SS).


(*
% Since there were some redundacies, we re-formulate some predicates that should be generated.
%% not  needed since Feb 28

pred gennat (nat).

gennat(z).
gennat(X28) => gennat(sc(X28)).

pred genmbool (mbool).

genmbool(mfalse).
genmbool(mtrue).

pred genlist [(id,nat)].
genlist([]).
gennat(N), genlist(Rest) => genlist([(X,N)|Rest]).


% same problem with NE

pred neqnat ((nat,nat)).

neqnat(sc(_),z).
neqnat(z,sc(_)).
neqnat(X55,Y56) => neqnat(sc(X55),sc(Y56)).


pred neq_state (([(id,nat)],[(id,nat)])).
neq_state([],[_|_]).
neq_state([_|_],[]).
(exists X61:id. (exists X62:id. (exists X63:nat. (exists X64:nat. X157 = (X61,X63), (Y159 = (X62,X64), (X61 # X62 ; neqnat(X63,X64))))))) ; neq_state(X258,Y260) => neq_state([X157|X258],[Y159|Y260]).

*)
