%% nega indepemdemt checks for top Volpano
#check "confinement" 9: 
   eval(S,C,S'), 
   secty(L,T,C),
   same_dom(S,S',T) => simll(S,L,T,S').


#check "ni" 9: 
   secty(z,T,C),
   eval(S,C,S'), eval(Tau,C,Tau'), 
   same_dom(S,Tau,T),
   same_dom(S,S',T),
   simle(S,L,T,Tau)       =>    simle(S',L,T,Tau').

#check "antimono" 10:
    secty(L,T,C),
    le(L', L)    => secty(L',T,C).



