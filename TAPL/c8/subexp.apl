% counterexample to subject expansion


% sub expansion
#check "sexpand" 5 : has_type(M',T), step(M,M') => has_type(M,T).

(*

This means: are there M M' T such that  has_type(M',T), step(M,M') holds but  has_type(M,T) does not? Yes:

Checking depth 1 2 3 4Counterexample found:
M = tif(ttrue)(ttrue)(tzero) 
M' = ttrue 
T = tbool 

Total 0.006462
Running	0.
*)


