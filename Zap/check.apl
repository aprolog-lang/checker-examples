#check "step_det" 5 : step(ME,S,ME'), step(ME,S',ME''), state(ME),state(ME'),state(ME'') => S = S'.
#check "step1_det" 5 : simpleStep(ME,S,ME'), simpleStep(ME,S',ME''), state(ME),state(ME'),state(ME'') => S = S'.


% ok but long
#check "subst_fun" 5 :
subst(E,M,X) = E1,
subst(E,M,X) = E2 => E1 = E2.

#invalidate "fstep_det" 5 : fault(E,E1), fault(E,E2) => 
				      E1 = E2.

#check "lemma2" 10 : statetc(Z,(M,E),T),  heap(M)
	=> safe2(M,E).

#check "lemma3.1" 7 : tc(G,D,none,E,T)
	=> tc(G,D,some(C),E,T).
#check "lemma3.2" 10 : statetc(none,(M,E),T),heap(M)
	=> statetc(some(C),(M,E),T).

#check "lemma4" 10 : statetc(some Z,(M,E),T), simpleStep((M,E),S,(M',E')),
color(Z), heap(M), heap(M')
	=> statetc(some Z,(M',E'),T).

#check "lemma5.1" 10 : statetc(some Z,(M,E),T), step((M,E),S,(M',E')),
	color(Z), heap(M), heap(M')
	     => statetc(some Z,(M',E'),T).

#check "lemma5.2" 10 : 
statetc(none,(M,E),T), fault(E,E'),
	heap(M)
	=> exists_c_statetc((M,E'),T).

#check "lemma6" 10 : statetc(none,(M,E),T), fsteps((M,E),(M',E')),
	heap(M),heap(M')
	=> safe2(M',E').

#invalidate "2fault-breaks-lemma5.2" 10 : statetc(none,([],E),T), fault(E,E'), fault(E',E'')
	=> statetc(Z,([],E''),T).


