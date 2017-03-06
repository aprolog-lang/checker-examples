

%%% Syntax (fig. 6) µgft
var : name_type.
const : type.

pty : type.
unitTy : pty.
intTy : pty.

ty : type.
pty : pty -> ty.
pairTy : (ty, ty) -> ty.
funTy : (ty, ty) -> ty.
arrTy : (ty, ty) -> ty.

idC : const.
timesC : const.
assocC : const.
assocInvC : const.
compC : const.
dupC : const.
swapC : const.
juggleC : const.
transposeC : const.
shuffleC : const.
shuffleInvC : const.

traceC : const.

arrC : const.
seqC :  const.
firstC : const.
secondC : const.
loopC : const.
initC :  const.
loopBC : const.

exp : type.

var : var -> exp.
pair : (exp,exp) -> exp.
fst : exp -> exp.
snd : exp -> exp.
lam : (var\exp) -> exp.
app : (exp,exp) -> exp.
unit : exp.
const : const -> exp.


type ctx = [(var,ty)]. 

%%% Typing rules (fig. 6)

pred constTy (const,ty).
constTy(idC, funTy(A,A)).
constTy(timesC, funTy(funTy(A,B),funTy(funTy(C,D),funTy(pairTy(A,C),pairTy(B,D))))).
constTy(assocC,  funTy(pairTy(pairTy(A,B),G),pairTy(A,pairTy(B,G)))).
constTy(assocInvC, funTy(pairTy(A,pairTy(B,G)),pairTy(pairTy(A,B),G))).
constTy(compC,funTy(funTy(B,G), funTy(funTy(A,B), funTy(A,G)))).
constTy(dupC, funTy(A, pairTy(A,A))).
constTy(swapC, funTy(pairTy(A,B), pairTy(B,A))).
constTy(juggleC,funTy(pairTy(pairTy(A,B),C), pairTy(pairTy(A,C),B))).
constTy(transposeC, funTy(pairTy(pairTy(A,B),pairTy(C,D)), pairTy(pairTy(A,C),pairTy(B,D)))).
constTy(shuffleC, funTy(pairTy(A,pairTy(pairTy(B,C),pairTy(D,E))), pairTy(pairTy(A, pairTy(B,D)),pairTy(C,E)))).
constTy(shuffleInvC, funTy(pairTy(pairTy(A, pairTy(B,D)),pairTy(C,E)), pairTy(A,pairTy(pairTy(B,C),pairTy(D,E))))).

constTy(traceC, funTy(funTy(pairTy(A,C), pairTy(B,C)), funTy(A,B))).

constTy(arrC, 
        funTy(funTy(A,B),arrTy(A,B))).
constTy(seqC,
        funTy(arrTy(A,B),funTy(arrTy(B,G),arrTy(A,G)))).
constTy(firstC,
        funTy(arrTy(A,B), arrTy(pairTy(A,G),pairTy(B,G)))).
constTy(secondC,
        funTy(arrTy(A,B), arrTy(pairTy(C,A),pairTy(C,B)))).
constTy(loopC, 
        funTy(arrTy(pairTy(A,G),pairTy(B,G)),arrTy(A,B))).
constTy(initC, funTy(A,arrTy(A,A))).
constTy(loopBC,
     funTy(D,
           funTy(arrTy(pairTy(A,pairTy(C,D)),pairTy(B,pairTy(C,D))),
                 arrTy(A,B)))).





pred mem((var,ty),[(var,ty)]).
mem(X,[X'|Xs]) :- X = X'.
mem(Y,[X|Xs]) :- mem(Y,Xs).



pred tc (ctx,exp,ty).
tc(G,const(C),Ty) :- constTy(C,Ty).
tc(G,var(X),Ty) :- mem((X,Ty),G).
tc(G,unit,pty(unitTy)).
tc(G,lam(E),funTy(A,B)) :- new x. tc([(x,A)|G],E@x,B).
tc(G,app(E1,E2),B) :- exists A. tc(G,E1,funTy(A,B)), tc(G,E2,A).
tc(G,pair(E1,E2),pairTy(A,B)) :- tc(G,E1,A), tc(G,E2,B).
tc(G,fst(E),A) :- exists B. tc(G,E,pairTy(A,B)).
tc(G,snd(E),B) :- exists A. tc(G,E,pairTy(A,B)).

% Abbreviations

func id = exp.
id = const idC.

func comp exp exp = exp.
comp G F = app(app(const compC,G), F).

func times exp exp = exp.
times F G = app(app(const timesC,F), G).


% Function/ abbreviation versions of arrow constants

func arr(exp) = exp.
arr(E) = app(const(arrC),E).

func first(exp) = exp.
first(E) = app(const(firstC),E).

func seq exp exp = exp.
seq E1 E2  = app(app(const(seqC),E1),E2).

func loop(exp) = exp.
loop(E) = app(const(loopC),E).

func init(exp) = exp.
init(E) = app(const(initC),E).

% lots of type annotations omitted.
func second(exp) = exp.
second(E) = seq(seq(arr(const swapC)) (first(E))) (arr(const swapC)).


% Todo: juggle, transpose, shuffle, shuffleInv - needed for reductions


func loopB  exp exp = exp.
loopB I F = app(app(const loopBC, I), F).



% Constant Definitions

pred constDef(const,exp).
constDef(idC,E) :- E = lam(x\var(x)).
constDef(timesC, E ) :- E =
         lam(f\lam(g\lam(z\ pair(app(var f, fst (var z)), app(var g, snd(var(z))))))).
constDef(assocC, E ) :- E =
         lam(z\pair(fst(fst (var z)),pair(snd(fst(var z)), snd(var z)))).
constDef(assocInvC, E ) :- E =
         lam(z\pair(pair(fst(var z),fst(snd(var z))), snd(snd (var(z))))).
constDef(compC, E ) :- E =lam( f\
                           lam( g\
                             lam(x\app(var f,app(var g, var x))))).
constDef(dupC, E ) :- E =lam(x\pair(var x, var x)).
constDef(swapC, E ) :- E =lam(x\pair(snd(var x),fst(var x))).
constDef(juggleC, comp(const assocInvC) (comp (times id (const swapC)) (const assocC))).
constDef(transposeC, comp (const assocC) (comp (times (const juggleC) id) (const assocC))).
constDef(shuffleC, comp (const assocInvC) (times id (const transposeC))).
constDef(shuffleInvC, comp (times id (const transposeC)) (const assocC)).

% trace, arr, seq, first, second, loop, loopB, init are primitive

% Beta-reduction steps
% These are not stated in the CCA paper but are needed for normalization.
pred beta(exp,exp).
beta(fst(pair(X,Y)),X).
beta(snd(pair(X,Y)),Y).

% Reduction steps


pred red(exp,exp).
red(const(C),E) :- constDef(C,E).
red(E,E') :- beta(E,E').
red(loop F, loopB unit (seq (arr (const assocInvC)) (seq (first F) (arr (const assocC))))).
red(init I, loopB I (arr (comp (const swapC) (comp (const juggleC) (const swapC))))).
red(seq (arr F) (arr G), arr (comp G F)).
red(first (arr F), arr (times F id)).
red(seq H (loopB I F), loopB I (seq (first H) F)).
red(seq (loopB I F) (arr G), loopB I (seq F (first (arr G)))).
red(loopB I (loopB J F), loopB (pair(I,J)) (seq (arr (const shuffleC)) (seq F (const shuffleInvC)))).
red(first(loopB I F), loopB I (seq (arr (const juggleC)) (seq (first F) (arr (const juggleC))))).

% Normalization

pred ccnf(exp).
ccnf(X) :- (exists Z. X = arr(Z)); (exists Y, Z. X = loopB Y (arr Z)).

pred norm(exp,exp).
norm(E,E') :- ccnf(E), E = E'.
norm(seq E1 E2, E') :-
	 exists E1'. norm(E1,E1'),
	 exists E2'. norm(E2,E2'),
	 exists E. red(seq E1 E2, E), norm(E, E').
norm(first(F),E') :- exists F'. norm(F,F'), exists E. red(first(F'),E), norm(E,E').
norm(init(I),E') :- exists E. red(init(I),E), norm(E,E').
norm(loop(F),E') :- exists E. red(loop(F),E), norm(E,E').
norm(loopB I F, E') :- exists F'. norm(F,F'), exists E. red(loopB I F', E), norm(E,E').


% Equivalence laws
% Some terms are left as variables for now and need to be filled in.

pred equiv(exp,exp).
% Lambda calculus laws
equiv(const C, D) :- constDef(C,D).
equiv(E,E') :- beta(E,E').
% more TODO

% Arrow laws
equiv(seq (arr id) F, F') :- F = F'.
equiv(seq F (arr id), F') :- F = F'.
equiv(seq (seq F G) H, X) :- exists F'. X = seq F' (seq G H).
equiv(arr (comp G F), X) :- X = seq (arr F) (arr G).
equiv(first(arr F), X) :- X = arr(times F id).
equiv(first(seq F G), X) :- X = seq (first F) (first G).
equiv(seq (first F) (arr (times id G)), X) :- X = seq (arr (times id G)) (first F).
equiv(seq (first F) (arr (const firstC)), X) :- X = seq (arr (const firstC)) F.
equiv(seq (first (first F)) (arr (const assocC)), X) :- X = seq (arr (const assocC)) (first F).

% Loop laws
equiv(loop(seq (first H) F),seq H' (loop F')) :- F = F', H = H'.
equiv(loop(seq F (first H)),  seq (loop F') H') :- F = F', H = H'.
equiv(loop(seq F (arr (times id K))), loop (seq (arr (times id K')) F')) :- K = K', F = F'.
equiv(loop(loop F), loop (seq (arr (const assocInvC)) (seq F (arr (const assocC))))).
equiv(second(loop F), loop (seq (arr (const assocC)) (seq (second F) (arr (const assocInvC))))).
equiv(loop (arr F), arr TraceF).

%% CCA laws
equiv(seq(first F) (second G), seq (second G) (first F)).
equiv(seq(first (init I)) (second (init J)), init (pair(I,J))).









