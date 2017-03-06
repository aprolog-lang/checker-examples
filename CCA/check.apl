
pred exists_norm(exp).
exists_norm(E) :- exists X. norm(E,X).




% can't check for termination but can check for missing cases
#check "norm_exists" 10 : tc([],E,arrTy(A,B))       => exists_norm(E).

#check "red_equiv" 12 : red(E,E'), tc([],E,arrTy(A,B))        => equiv(E,E').






