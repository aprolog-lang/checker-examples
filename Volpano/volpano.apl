%% Volpano's sec types, following Nipkow & Klein Concrete Semantics
%% Author: AM (debugged)

%%% levels are nats

type level = nat.

% I define a function in order to make ne-simpl work (if-then-else nor ! not
% yet supported)
func maxf (level,level) = level.
maxf(L1,L2) = L2 :- le(L1,L2), !.
maxf(L1,L2) = L1.

pred max  (level,level, level).
max(L1,L2,L2) :- le(L1,L2).
% max(L1,L2,L1) :- gt(L1,L2).
max(L1,L2,L1) :- le(L2,L1).


func minf (level,level) = level.
minf(L1,L2) = L1 :- le(L1,L2), !.
minf(L1,L2) = L2.

pred min  (level,level, level).
min(L1,L2,L1) :- le(L1,L2).
min(L1,L2,L2) :- gt(L1,L2).




%%  a data structure for vars to set security levels
%% cannot use a predicate because of equivariance

type sectx = [(id,level)].

pred lookup(sectx,id,level).
lookup([(X,L) | _ ], X, L).
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
  secty(L,T,C1),secty(L,T,C2).

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

% without guards
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


%% same stuff but with strictly less

pred simllg(state,level,sectx,state).

simllg([],_,_,[]).
simllg([(X,V1)|S1],L,T,[(X',V2)|S2]) :-
  X = X',
 ((exists Lx. lookup(T,X,Lx),
 ll(Lx,L)) -> V1 = V2,   simllg(S1,L,T,S2)
              | simllg(S1,L,T,S2)).


pred simll(state,level,sectx,state).
simll([],_,_,[]).
simll([(X,V)|S1],L,T,[(X,V)|S2]) :-
 (exists Lx. lookup(T,X,Lx),
 ll(Lx,L)), 
 simll(S1,L,T,S2).
simll([(X,_)|S1],L,T,[(X,_)|S2]) :-
 (exists Lx. lookup(T,X,Lx),
  le(L,Lx)),
  simll(S1,L,T,S2).
% simll([(X,V)|S1],L,T,[(X',V')|S2]) :-
%   X = X',
%   (exists Lx. lookup(T,X,Lx),
%  ll(Lx,L)),
%  V = V', 
%  simll(S1,L,T,S2).
% simll([(X,_)|S1],L,T,[(X',_)|S2]) :-
%   X = X',
%  (exists Lx. lookup(T,X,Lx),
%   le(L,Lx)),
%   simll(S1,L,T,S2).



% states and tables have same domain and are well formed as assoc lists
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





func maxf  (level,level) = level.
maxf(L1,L2) = L2' :- le(L1,L2), L2 = L2'.
maxf(L1,L2) = L1' :- ll(L2,L1), L1 = L1'.




pred foo(state,level,sectx,state). 

foo([],_,_,[]).
foo([(X,V1)|S1],L,T,[(X',V2)|S2]) :-
 ((exists Lx. 
  V1 = V2 -> V1 = V2
              | V1 = V2)).
*)
