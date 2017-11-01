%% We just check type uniqueness here
%% usual checks go thru, commented out

#check "ty_uniq" 7  : tc([],E,T), tc([],E,T') => T = T'.

% #check "ty_uniq_open" 7  : tc(G,E,T), tc(G,E,T'), valid_ctx(G) => T = T'.
% same result, only slower
/*


#check "sub_fun" 5  : subst(M,x,N) = M1, subst(M,x,N) = M2 => M1 = M2.

#check "sub_id"  7   : subst(M,x,var(x)) = M.

#check "sub_fresh" 4 : x # M => subst(M,x,N) = M.

#check "sub_comm" 3  :
	x # N'
	 =>
        subst(subst(M,x,N),y,N') = subst(subst(M,y,N'),x,subst(N,y,N')).

#check "tc_weak" 5 : tc(G,E,T),valid_ctx(G) =>
                     new x. tc([(x,T')|G],E,T).

#check "tc_subst"  4 : x # (G,E), tc(G,E,T), tc([(x,T)|G],E',T'),
                     valid_ctx(G)  =>
                     tc(G,subst(E',x,E),T').

#check "tc_pres" 6 : tc([],M,T), step(M,M') => tc([],M',T).

#check "tc_prog" 8 : tc([],E,T) => progress(E).

#check "tc_sound" 7 : tc([],E,T), steps(E,E') => tc([],E',T).


*/
