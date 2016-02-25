%% Volpano's sec types, following Nipkow & Klein Concrete Semantics
%% Author: AM
%% NIP BUG

%%% levels are nats

type level = nat.

% not using if then else
pred max  (level,level, level).
max(L1,L2, L2') :- 
  (le(L1,L2) ->  L2 = L2' | L2' = L1).


pred min  (level,level, level).
min(L1,L2, L2') :- 
    (le(L1,L2) ->  L1 = L2' | L2' = L2).

%%  a table for vars to set security levels
type sectx = [(id,level)].

pred lookup(sectx,id,level).
lookup([(X,L) | _ ], Y, L') :- X = Y, L = L'.
lookup([(X,_) | Ts], Y, L) :- X # Y, lookup(Ts,Y,L).

%% assigning sec levels to a(b)exp
pred asec(aexp, sectx,level).
asec(c(N), _,z).
asec(var X,T, L):- lookup(T,X,L).
asec(plus(A1,A2), T,L) :- 
  exists L1. asec(A1,T, L1), 
  exists L2. asec(A2,T,L2),  
  max(L1,L2,L).

pred bsec(bexp, sectx,level).
bsec(b(N), T, z).
bsec(cnot B,T, L) :- bsec (B,T,L).
bsec(less(A1,A2),T, L) :- 
  exists L1. asec(A1,T,L1),
  exists L2. asec(A2,T,L2), 
   max(L1,L2,L).
bsec(cand(B1,B2),T, L) :- 
  exists L1. bsec(B1,T, L1),
  exists L2. bsec(B2,T, L2),  
  max(L1,L2,L).


% typing
pred secty (level,sectx,cmd).

secty(_,_,skip).

secty(L,T,assn(X,A)) :- 
  exists LX. lookup(T,X,LX), 
  exists LA. asec(A, T, LA), 
  le(LA,LX), le(L,LX).

secty(L,T,seq(C1,C2)) :- 
  secty(L,T,C1). %%,secty(L,T,C2). BUG

secty(L,T,ift(B,C1,C2)) :- 
  exists Lb. bsec(B,T, Lb), 
  exists Max. max(Lb,L,Max), 
  secty(Max,T, C1),
  secty(Max,T, C2).

secty(L,T,whi(B,C)) :- 
  exists Lb. bsec(B,T, Lb),
  exists Max. max(Lb,L,Max),
  secty(Max,T, C). 


% tests
% T = [(x0,z),(x1,sc z), (x2, sc (sc z))], secty(z,T,assn(x1, var x0)).
%  T = [(x0,z),(x1,sc z), (x2, sc (sc z))], secty(z,T,assn(x0,c(z))). % yes
% T = [(x0,z),(x1,sc z), (x2, sc (sc z))], secty(z,T,assn(x2, var x0)). % yes
% T = [(x0,z),(x1,sc z), (x2, sc (sc z))], secty(z,T,assn(x0, var x2)). % no



%%% non interference

%% assume states and sectx have same  domain in same order

(*
 s1 is related to s2 wrt <= (or <) l iff for all x s.t. sec x <= (or <) l -> s1 x = s2 x
*)

% guarded: WARNING: do not use under NF with nested negation as in
%  non-intereference

pred simleg(state,level,sectx,state).

simleg([],_,_,[]).
simleg([(X,V1)|S1],L,T,[(X',V2)|S2]) :-
  X = X',
 ((exists Lx. lookup(T,X,Lx),
  le(Lx,L)) -> V1 = V2,   simleg(S1,L,T,S2)
              | simleg(S1,L,T,S2)).


pred simle(state,level,sectx,state).
simle([],_,_,[]).
simle([(X,V1)|S1],L,T,[(X',V2)|S2]) :-
  X = X',
  (exists Lx. lookup(T,X,Lx),
 le(Lx,L)), 
  V1 = V2,  
  simle(S1,L,T,S2).

simle([(X,_)|S1],L,T,[(X',_)|S2]) :-
  X = X',
( exists Lx. lookup(T,X,Lx),
  ll(L,Lx)),
  simle(S1,L,T,S2).


%% assume states and sectx have same (ordered) domain 


pred simllg(state,level,sectx,state).

simllg([],_,_,[]).
simllg([(X,V1)|S1],L,T,[(X',V2)|S2]) :-
  X = X',
 ((exists Lx. lookup(T,X,Lx),
 ll(Lx,L)) -> V1 = V2,   simllg(S1,L,T,S2)
              | simllg(S1,L,T,S2)).


pred simll(state,level,sectx,state).
simll([],_,_,[]).
simll([(X,V)|S1],L,T,[(X',V')|S2]) :-
  X = X',
  (exists Lx. lookup(T,X,Lx),
 ll(Lx,L)),
 V = V', 
 simll(S1,L,T,S2).
simll([(X,_)|S1],L,T,[(X',_)|S2]) :-
  X = X',
 (exists Lx. lookup(T,X,Lx),
  le(L,Lx)),
  simll(S1,L,T,S2).



% states and table have same domain and are well formed as assoc lists
pred same_dom(state,state,sectx).

same_dom([],[],[]).
same_dom([(X,_)|S],[(X1,_)|S'],[(X2,_)|T])
 :- X = X1, X1 = X2, 
  X # S, X # S', X # T, 
  same_dom(S,S',T). 

(*
 secty(z, [(X,sc(sc(z)))] ,assn(X,c(z))).
Yes.

?- not_secty(z, [(X,sc(sc(z)))] ,assn(X,c(z))).

yes

?- secty(z, [(x1,sc(sc(z)))] ,assn(x1,c(z))).
Yes.

?- not_secty(z, [(x1,sc(sc(z)))] ,assn(x1,c(z))).
Yes.
 not_secty(z, [(X1250,sc(sc(_1398)))|_1260] ,assn(X1250,c(N1269))).
Fatal error: exception Stack_overflow


secty(L,T,ift(B,C1,C2)) :- 
  exists Lb. bsec(B,Lb), 
  le(Lb,L), 
  secty(L,T, C1),
  secty(L,T, C2).
secty(L,T,ift(B,C1,C2)) :- exists Lb. bsec(B,Lb), ll(L,Lb), secty(Lb,T, C1),secty(Lb,T, C2).
secty(L,T,whi(B,C)) :- exists Lb. bsec(B,Lb), le(Lb,L), secty(L,T, C).
secty(L,T,whi(B,C)) :- exists Lb. bsec(B,Lb), ll(L,Lb), secty(Lb,T, C).




(*

%func  xsec  (sectx,id) = nat.
%xsec (T,X) = L :- lookup(T,X,L).

% xsec([(x0,z),(x1,sc z), (x2, sc (sc z))],x1) = L.


max(L1,L2, L2') :- le(L1,L2), L2 = L2'.
max(L1,L2,L1') :- ll(L2,L1), L1 = L1'.

func maxf  (level,level) = level.
maxf(L1,L2) = L2' :- le(L1,L2), L2 = L2'.
maxf(L1,L2) = L1' :- ll(L2,L1), L1 = L1'.
*)

*)


% NF on non-interference
% depth 8
% Total: 14.879214 s:
% C = seq(skip,assn(X3370103,var(X3369781))) 
% L = z 
% S = [(X3369781,sc(z)),(X3370103,_3361740)] 
% S' = [(X3369781,sc(z)),(X3370103,sc(z))] 
% T = [(X3369781,sc(sc(sc(z)))),(X3370103,z)] 
% Tau = [(X3369781,z),(X3370103,_3361740)] 
% Tau' = [(X3369781,z),(X3370103,z)] 

  
% NEj on non-interference
% depth 8
% Total: 11.659299 s:
% C = seq(skip,assn(X22015589,var(X22015634))) 
% L = z 
% S = [(X22015589,_2015444),(X22015634,sc(sc(_2020290)))] 
% S' = [(X22015589,sc(sc(_2020290))),(X22015634,sc(sc(_2020290)))] 
% T = [(X22015589,z),(X22015634,sc(_2019722))] 
% Tau = [(X22015589,_2015444),(X22015634,sc(z))] 
% Tau' = [(X22015589,sc(z)),(X22015634,sc(z))] 

% NEs the same of NEj
