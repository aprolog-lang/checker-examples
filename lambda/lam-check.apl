%% Neg independent checks -- may not be  the best orderings

#check "sub_fun" 5  : subst(M,x,N) = M1, subst(M,x,N) = M2 => M1 = M2.

#check "sub_id"  7   : subst(M,x,var(x)) = M.

#check "sub_fresh" 4 : x # M => subst(M,x,N) = M.

#check "sub_comm" 4  : 
	x # N',
	X0 = subst(M,x,N),
	Y0 = subst(M,y,N'),
	Y = subst(Y0,x,Y1),
	X = subst(X0,y,N'),
	Y1 = subst(N,y,N')
	 => 
        X = Y.
#check "tc_weak" 5 : tc(G,E,T),valid_ctx(G) => 
                     new x. tc([(x,T')|G],E,T).

#check "tc_subst"  4 : x # (G,E), tc(G,E,T), tc([(x,T)|G],E',T'),
                     valid_ctx(G), E'' = subst(E',x,E) => 
                     tc(G,E'',T').

#check "tc_pres" 6 : tc([],M,T), step(M,M') => tc([],M',T).

#check "tc_prog" 8 : tc([],E,T) => progress(E).

#check "tc_sound" 6 : tc([],E,T), steps(E,E') => tc([],E',T).
