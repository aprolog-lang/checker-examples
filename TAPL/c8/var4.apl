(*
Suppose instead that we add this rule:
      | ST_Funny3 : 
          (tpred tfalse) ⇒ (tpred (tpred tfalse))

All remain true

*)

step((tpred tfalse),(tpred (tpred tfalse))).

% -> none get falsified as expected in both NE/NF
