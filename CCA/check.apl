
pred exists_norm(exp).
exists_norm(E) :- exists X. norm(E,X).

% can't check for termination but can check for missing cases
#check "norm_exists" 6 : tc([],E,arrTy(A,B))       => exists_norm(E).

#check "red_equiv" 4 : red(E,E'), tc([],E,arrTy(A,B))        => equiv(E,E').






