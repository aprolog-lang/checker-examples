%% basic NE checks, with the best goal orderings (especially wrt TESS)


#check "subst_fun" 5 : not_substp(M,x,N,M0), subst(M,x,N) = M0 => false.


#check "sub_id" 7    : not_substp(M,x,var(x),M) => false.


#check "subst_fresh" 7 : x # M, not_substp(M,x,N,M) => false.


#check "sub_comm" 4 : 
	x # N',
	not_substp(X0,y,N',Y),
	X0 = subst(M,x,N),
	Y0 = subst(M,y,N'),
	Y = subst(Y0,x,Y1),
	Y1 = subst(N,y,N')
	 =>   false.


#check "tc_weak" 5  : x # G, tc(G,M,T),
                     not_tc([(x,U)|G],M,T), valid_ctx(G) => false. 


#check "tc_subst" 4 : x # G, N' = subst(N,x,M), tc([(x,T)|G],N,U), 
                     tc(G,M,T),  not_tc(G,N',U), valid_ctx(G) => false.


#check "tc_pres" 6 : tc([],M,T),step(M,M'),not_tc([],M',T)  => false.

#check "tc_prog" 8 : not_progress(E), tc([],E,T) => false.

#check "tc_sound" 6 :  tc([],E,T), steps(E,E'), not_tc([],E',T) => false.

