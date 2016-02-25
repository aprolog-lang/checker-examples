(* SF:

Suppose instead that we add this rule:
      | T_Funny4 : 
            ⊢ tzero ∈ TBool


    Progress becomes false: tif tzero ttrue ttrue has type TBool, is a normal form, and is not a value.

*)

has_type((tzero,tbool)).

(*

NF 
Checking depth 1 2 3 4
progress:

M = tif(tzero)(ttrue)(ttrue) 
T = tbool

Total: 0.002212 s:
Note that trivially also type uniqueness fails


Total: 0.002435 s:
E = tzero 
T1 = tnat 
T2 = tbool 


same with NE

*)
