#check "has_det" 7 : has_type(E,T1),has_type(E,T2) => T1 = T2.
#check "step_det" 7 : step(E,E1),step(E,E2) => E1 = E2.
#check "preservation" 7 : has_type(M,T), step(M,M')  => has_type(M',T).
#check "progress" 8 : has_type(E,T)=> nstuck(E).

