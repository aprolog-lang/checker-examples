(*SF:
Suppose instead that we add this rule:
      | ST_Funny2 : ∀t1 t2 t2' t3,
           t2 ⇒ t2' →
           (tif t1 t2 t3) ⇒ (tif t1 t2' t3)


    Determinism again becomes false: tif tfalse (tpred tzero) (tsucc tzero) can now evaluate in one step to either tsucc tzero or tif tfalse tzero (tsucc tzero). (There are several other correct counter-examples.)

*)

step((tif T1 T2 T3),(tif T1' T2' T3')):- T1 = T1', T3 = T3', step(T2,T2').

(*
NF -- 
Total: 0.107618 s:
E = tif(ttrue)(tif(ttrue)(tzero)(tzero))(tfalse) 
E1 = tif(ttrue)(tzero)(tzero) 
E2 = tif(ttrue)(tzero)(tfalse) 

NE:

Total: 0.004 s:
E = tif(ttrue)(tif(ttrue)(T2'1232)(tiszero(_1702)))(tpred(_1700)) 
E1 = tif(ttrue)(T2'1232)(tiszero(_1702)) 
E2 = tif(ttrue)(T2'1232)(tpred(_1700)) 

*)
