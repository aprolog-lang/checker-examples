#check "lem3.2(1)" 10 : 
  alg_eq_o(G,M,N,T), x # G, x # M, x # N, x # T, x # T', wf_sctx([(x,T')|G]) => alg_eq_o([(x,T')|G],M,N,T).

#check "lem3.2(2)" 10 : 
  str_eq_o(G,M,N,T), x # G, x # M, x # N, x # T, x # T', wf_sctx([(x,T')|G]) => str_eq_o([(x,T')|G],M,N,T).

#check "lem3.2(3)" 10 : 
  alg_eq_t(G,M,N,T), x # G, x # M, x # N, x # T, x # T', wf_sctx([(x,T')|G]) => alg_eq_t([(x,T')|G],M,N,T).
#check "lem3.2(4)" 10 : 
  str_eq_t(G,M,N,T), x # G, x # M, x # N, x # T, x # T', wf_sctx([(x,T')|G]) => str_eq_t([(x,T')|G],M,N,T).

#check "lem3.2(5)" 10 : 
  alg_eq_k(G,M,N), x # G, x # M, x # N, x # T, x # T', wf_sctx([(x,T')|G]) =>  alg_eq_k([(x,T')|G],M,N).

#check "lem3.3(1)" 10: whr(M,M'), whr(M,M'') => M' = M''.

#check "lem3.3(2)" 10 : 
  str_eq_o(D,M,N,T) => whnf(M).
#check "lem3.3(3)" 10 : 
  str_eq_o(D,M,N,T) => whnf(N).
#check "lem3.3(4)" 10 : 
  str_eq_o(D,M,N,T), str_eq_o(D,M,N,T'), wf_sctx(D) => T = T'.
#check "lem3.3(5)" 10 : 
  str_eq_t(D,M,N,K), str_eq_t(D,M,N,K'), wf_sctx(D) => K = K'.


(* Symmetry *)

#check "lem3.4(1)" 10:
  str_eq_o(D,M,N,T), wf_sctx(D) => str_eq_o(D,N,M,T).
#check "lem3.4(2)" 10:
  alg_eq_o(D,M,N,T), wf_sctx(D) => alg_eq_o(D,N,M,T).
#check "lem3.4(3)" 10:
  str_eq_t(D,M,N,T), wf_sctx(D) => str_eq_t(D,N,M,T).
#check "lem3.4(4)" 10:
  alg_eq_t(D,M,N,T), wf_sctx(D) => alg_eq_t(D,N,M,T).
#check "lem3.4(5)" 10:
  alg_eq_k(D,K,K'), wf_sctx(D) => alg_eq_k(D,K',K).

(* Transitivity *)

#check "lem3.5(1)" 8 :
  str_eq_o(D,M,N,T), str_eq_o(D,N,O,T), 
  wf_sctx(D)  => str_eq_o(D,M,O,T).
#check "lem3.5(2)" 8:
  alg_eq_o(D,M,N,T), alg_eq_o(D,N,O,T) , 
  wf_sctx(D) => alg_eq_o(D,M,O,T).

#check "lem3.5(3)" 8:
  str_eq_t(D,M,N,T), str_eq_t(D,N,O,T) , 
  wf_sctx(D)  => str_eq_t(D,M,O,T).
#check "lem3.5(4)" 8:
  alg_eq_t(D,M,N,T), alg_eq_t(D,N,O,T) , 
  wf_sctx(D)  => alg_eq_t(D,M,O,T).

#check "lem3.5(5)" 8:
  alg_eq_k(D,M,N), alg_eq_k(D,N,O), 
  wf_sctx(D)  => alg_eq_k(D,M,O).

