#check "tc_prog" 8 : tc([],E,T), gen_exp(E) => progress(E).
#check "tc_proggfst" 8 :  gen_exp(E),tc([],E,T) => progress(E).

#check "tc_sound" 7 : tc([],E,T), steps(E,E') , gen_ty(T), gen_exp(E') => tc([],E',T).

#check "tc_sound_ebt" 7 : tc([],E,T), steps(E,E') ,  gen_exp(E'), gen_ty(T) => tc([],E',T). 
#check "tc_sound_stepsfst" 7 :  steps(E,E'), tc([],E,T), gen_ty(T), gen_exp(E') => tc([],E',T).


#check "tc_sound_gtfst" 7 :   gen_ty(T), tc([],E,T), gen_exp(E'), steps(E,E') => tc([],E',T).
#check "tc_sound_gstepfst**" 7 :   gen_ty(T), tc([],E,T) , steps(E,E'),gen_exp(E') => tc([],E',T).


#check "tc_sound_gtefst" 7 :   gen_ty(T), gen_exp(E'), tc([],E,T), steps(E,E') => tc([],E',T).
#check "tc_sound_getfst" 7 :  gen_exp(E'), gen_ty(T), tc([],E,T), steps(E,E') => tc([],E',T).
