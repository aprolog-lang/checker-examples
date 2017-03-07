#check "tc_pres" 11 : 
  tc([],M,T), step(M,M')  => tc([],M',T).

#check "tc_prog" 12 : tc([],E,T) => progress(E).
