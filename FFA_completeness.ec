require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import JUtils JBigNum.

require import FFA FFA_soundness AuxResults. 


import BN.
import Word.

lemma nosmt multiplication_completeness (M : int -> int) 
    (M_size p t1 t2 : int) (x y z : Word.t A.t) : 

    (forall i,  0 < M i)

    => 0 < q
 
    => K_max - K_min < 2 ^ t1
        
    => (forall i, 0 <= i < M_size =>
          (L_max (M i)) - (L_min (M i) (2 ^ t1)) 
           < (2 ^ t2))

    => (forall i, 0 <= i < M_size => 
         (-p) < AuxLB (M i) (K_min) 
                  (L_min (M i) (2 ^ t1)) 
                  (2 ^ t1) 
                  (2 ^ t2))

   => (forall i, 0 <= i < M_size => 
        AuxUB (M i) 
                (K_min) 
                (L_min (M i) (2 ^ t1)) < p)
      
  => (B - 1) * (sigma (fun (i : int) => 
       (B ^ i %% q))) + (2 ^ t1 + K_min) * q
       < LCM (fun i => if i = M_size then p else M i) 
             (M_size + 1)


  => (B - 1) ^ 2 *              
        (sigma (fun (i : int) => 
          sigma (fun (j : int) => 
            (B ^ (i + j) %% q)))) - ((K_min) * q)
        < LCM (fun i => if i = M_size then p else M i) 
              (M_size + 1)

  
  => ((bn x) * (bn y)) %% q = (bn z) %% q
    (* k and V are existential, depend on x y z *)
  => 0 < q 
  => exists k,
     0 <= U k < 2 ^ t1
    /\ (NativeLHS (K_min) (U k) x y z) %% p = 0

  
    /\ forall i, 0 <= i < M_size => exists V, 
       (0 <= V < 2 ^ t2)
    /\ ((AuxLHS
             (M i)
             V
             (K_min)
             (L_min (M i) (2 ^ t1))
             (U k)
             x y z) %% p = 0).

proof.
move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

move : H9.

rewrite first_step.

have -> : sigma
  (fun (i : int) =>
     sigma
       (fun (j : int) =>
          (to_uint x.[i]) * (to_uint y.[j]) * B ^ (i + j))) %% q
   = sigma
  (fun (i : int) =>
     sigma
       (fun (j : int) =>
          (to_uint x.[i]) * (to_uint y.[j]) * (B ^ (i + j) %% q))) %% q.
rewrite /sigma big_mod => /=.
have -> : (fun (x0 : int) =>
     bigi predT
       (fun (j : int) => to_uint x.[x0] * to_uint y.[j] * B ^ (x0 + j)) 0
       nlimbs %%
     q) = (fun (x0 : int) =>
     bigi predT
       (fun (j : int) => to_uint x.[x0] * to_uint y.[j] * (B ^ (x0 + j) %% q)) 0
       nlimbs %% q).
apply fun_ext. move => x0. rewrite   big_mod => /=.
have -> : (fun (x1 : int) => to_uint x.[x0] * to_uint y.[x1] * B ^ (x0 + x1) %% q)
      = (fun (x1 : int) => to_uint x.[x0] * to_uint y.[x1] * (B ^ (x0 + x1) %% q) %% q).
      apply fun_ext. move => x1.  by rewrite - modzMmr.
rewrite  - big_mod => /=. auto.
      rewrite  - big_mod => /=. auto. auto.
rewrite /bnk /dig.
have ->: bigi predT (fun (i : int) => to_uint z.[i] * B ^ i) 0 nlimbs %% q
       = sigma (fun (i : int) => to_uint z.[i] * (B ^ i %% q))  %% q.
      rewrite  big_mod => //.
have ->: (fun (x0 : int) => (fun (i : int) => to_uint z.[i] * B ^ i) x0 %% q) = (fun (x0 : int) => (fun (i : int) => to_uint z.[i] * (B ^ i %% q)) x0 %% q). apply fun_ext. move => x1. by rewrite - modzMmr. simplify.
      rewrite -  big_mod => //.

rewrite - min_eq.       
move => h.
have o : (sigma
     (fun (i : int) =>
        sigma
          (fun (j : int) =>
             to_uint x.[i] * to_uint y.[j] * (B ^ (i + j) %% q))) %%
   q - sigma (fun (i : int) => to_uint z.[i] * (B ^ i %% q)) %% q) %% q = 0.
apply wekenq. apply h. clear h.
move : o.
rewrite modzBmr.
rewrite modzBmr2.

move => h.
have : exists k, (sigma
   (fun (i : int) =>
      sigma
        (fun (j : int) => to_uint x.[i] * to_uint y.[j] * (B ^ (i + j) %% q))) -
 sigma (fun (i : int) => to_uint z.[i] * (B ^ i %% q))) = k * q.
      
apply  eqmodP0.  apply h.
elim. move => k kprop.    
exists k.
have ukq_bounds : (0 <= U k && U k < 2 ^ t1).
split.
 rewrite /U.
have -> : k = (sigma
         (fun (i : int) =>
            sigma
              (fun (j : int) =>
                 to_uint x.[i] * to_uint y.[j] * (B ^ (i + j) %% q))) -
       sigma (fun (i : int) => to_uint z.[i] * (B ^ i %% q))) %/ q.
apply muldivaux. smt(). apply kprop.
rewrite /K_min.          
apply (ltemul _ _ q). smt(). simplify.
rewrite mulrDl.
rewrite compl1. smt(). rewrite kprop.
apply dvdzP. exists k. auto.

have ->: (- (-1) * ((B - 1) * sigma (fun (i : int) => B ^ i %% q) %/ q))
          = (((B - 1) * sigma (fun (i : int) => B ^ i %% q) %/ q)). smt().

apply compl2.
apply miguels. auto.
rewrite kprop.
apply dvdzP. exists k. auto. 
rewrite lhsub1.
rewrite lhsub2.
simplify.
apply ltr_weaken. 
      + apply sumr_ge0. progress. rewrite /B.
      + apply sumr_ge0. progress.
        apply mul_pos.
        + smt(@Word).
      apply modz_ge0. smt().
apply lower_bound. smt().

progress.

rewrite /U.

have : k <= K_max. rewrite /K_max.
 have -> : k = (sigma
         (fun (i : int) =>
            sigma
              (fun (j : int) =>
                 to_uint x.[i] * to_uint y.[j] * (B ^ (i + j) %% q))) -
       sigma (fun (i : int) => to_uint z.[i] * (B ^ i %% q))) %/ q.
apply muldivaux. smt(). auto.
apply bounds2. smt().
apply ltr_weaken.
apply sumr_ge0. progress.
        apply mul_pos. smt(@Word). smt(@Int).
apply upper_bound. smt().
smt().
rewrite ukq_bounds. simplify.          
split.
rewrite /NativeLHS.
rewrite /U.
apply wekenq.
apply min_eq.
rewrite kprop.
smt().          
          
move => i iprop.
rewrite /AuxLHS.          
have Mimodeq : 
  (sigma
       (fun (i0 : int) =>
          sigma
            (fun (j : int) =>
               to_uint x.[i0] * to_uint y.[j] * (B ^ (i0 + j) %% q %% M i))) -
     sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q %% M i)) -
     U k * (q %% M i) - K_min * q %% M i) %% M i = 0.

have <- : (sigma
       (fun (i0 : int) =>
          sigma
            (fun (j : int) =>
               to_uint x.[i0] * to_uint y.[j] * (B ^ (i0 + j) %% q))) -
     sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q)) -
     U k * q - K_min * q) %% M i = (sigma
       (fun (i0 : int) =>
          sigma
            (fun (j : int) =>
               to_uint x.[i0] * to_uint y.[j] * (B ^ (i0 + j) %% q %% M i))) -
     sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q %% M i)) -
     U k * (q %% M i) - K_min * q %% M i) %% M i
   .
rewrite min_min2.
  have ->: U k * q %% M i = U k * (q %% M i) %% M i. by rewrite - modzMmr.
  have ->: (sigma
    (fun (i0 : int) =>
       sigma
         (fun (j : int) =>
            to_uint x.[i0] * to_uint y.[j] * (B ^ (i0 + j) %% q))) -
  sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q))) %%
 M i = (sigma
    (fun (i0 : int) =>
       sigma
         (fun (j : int) =>
            to_uint x.[i0] * to_uint y.[j] * (B ^ (i0 + j) %% q %% M i))) -
  sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q %% M i))) %%
 M i.
  rewrite - modzBmr2 - modzBmr.
  have -> : sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q)) %% M i 
   = sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q %% M i)) %% M i.
   rewrite /sigma big_mod.
     have -> : (fun (x0 : int) =>
     (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q)) x0 %% M i)
       = (fun (x0 : int) =>
     (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q %% M i)) x0 %% M i).
   apply fun_ext. move => x0. simplify. rewrite - modzMmr. auto.
   rewrite - big_mod. auto.

   rewrite /sigma. rewrite big_mod. simplify.

   have -> : (fun (x0 : int) =>
      bigi predT
        (fun (j : int) =>
           to_uint x.[x0] * to_uint y.[j] * (B ^ (x0 + j) %% q)) 0 nlimbs %%
      M i) = (fun (x0 : int) =>
      bigi predT
        (fun (j : int) =>
           to_uint x.[x0] * to_uint y.[j] * (B ^ (x0 + j) %% q %% M i)) 0 nlimbs %%
      M i).
   apply fun_ext. move => x0.  rewrite big_mod. simplify.
   have -> : (fun (x1 : int) =>
     to_uint x.[x0] * to_uint y.[x1] * (B ^ (x0 + x1) %% q) %% M i) =
    (fun (x1 : int) =>
     to_uint x.[x0] * to_uint y.[x1] * (B ^ (x0 + x1) %% q %% M i) %% M i).
    apply fun_ext. move => x1. rewrite - modzMmr. auto.
    rewrite - big_mod. auto.
    rewrite - big_mod.
    rewrite  modzBmr. rewrite modzBmr2. auto.
   auto.

   rewrite  min_min. 
auto.

rewrite kprop.
smt(@Int).
        
print dvdzP.          
print eqmodP0.
(* apply  eqmodP0.  apply h. *)
have : exists V, (sigma
            (fun (i0 : int) =>
               sigma
                 (fun (j : int) =>
                    to_uint x.[i0] * to_uint y.[j] *
                    (B ^ (i0 + j) %% q %% M i))) -
          sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q %% M i)) -
          U k * (q %% M i) - K_min * q %% M i) = V * M i.
apply  eqmodP0. assumption.
elim. move => V.
move => Vp.
exists (V - L_min (M i) (2 ^ t1)).
split.
split.

rewrite (muldivaux _ _ _ _ Vp). smt().


apply (ltemul _ _ (M i)). smt(). simplify.
rewrite mulrDl.
rewrite compl1. smt(). rewrite Vp.
apply dvdzP. exists V. auto.

rewrite /L_min.
have ->: (- (-1) *
   (((B - 1) * sigma (fun (i0 : int) => B ^ i0 %% q %% M i) +
     2 ^ t1 * (q %% M i) + K_min * q %% M i) %/
    M i))
          = (
   (((B - 1) * sigma (fun (i0 : int) => B ^ i0 %% q %% M i) +
     2 ^ t1 * (q %% M i) + K_min * q %% M i) %/
    M i)). smt().

apply compl2.
apply miguels. 
smt().
rewrite Vp.
apply dvdzP. exists V. auto. 
rewrite lhsub1.
rewrite lhsub2.

simplify.
have -> : (B - 1) * sigma (fun (i0 : int) => B ^ i0 %% q %% M i) + 2 ^ t1 * (q %% M i) +
K_min * q %% M i
  = K_min * q %% M i + ((B - 1) * sigma (fun (i0 : int) => B ^ i0 %% q %% M i) + 2 ^ t1 * (q %% M i)). smt().



rewrite popop.
rewrite popop.
rewrite ltr_plusc2.
rewrite popop2.

have -> : (B - 1) * sigma (fun (i0 : int) => B ^ i0 %% q %% M i) + 2 ^ t1 * (q %% M i) = 2 ^ t1 * (q %% M i) + (B - 1) * sigma (fun (i0 : int) => B ^ i0 %% q %% M i). smt().


  
rewrite popop4.
rewrite popop3. 

clear Mimodeq.
apply mul_leq. smt(@Int).
smt().  
apply ltr_weaken. 
      + apply sumr_ge0. progress. rewrite /B.
      + apply sumr_ge0. progress.
        apply mul_pos.
        + smt(@Word).
      apply modz_ge0. smt().

rewrite mulr_sumr.
apply ler_sum_seq => /=.
move => iz iin _.
apply ler_pmul => //.
   + smt(@Word).
   + apply modz_ge0 => //.
   + smt(@Word).
smt(@Word).

 move => vlowrbound.

have : V - L_min (M i) (2 ^ t1) <= L_max (M i) - L_min (M i) (2 ^ t1).
 apply popop5.
rewrite (muldivaux _ _ _ _ Vp). smt().
rewrite /L_max.  



apply bounds2. smt().
rewrite popop5.
apply ltr_weaken.  
apply mul_pos. smt(). smt(@Int).

apply ltr_weaken. 
apply sumr_ge0. progress. rewrite /B.         apply mul_pos.
  smt(@Word). smt(@Int).

rewrite mulr_sumr.
apply ler_sum_seq.
move => ik iin _ /=.
rewrite mulr_sumr.
apply ler_sum_seq.
move => j jin _ /=.
apply kk. 
 + apply modz_ge0 => //.  smt().
apply ler_pmul; smt(@Word). 
  

have : L_max (M i) - L_min (M i) (2 ^ t1) < 2 ^ t2. apply H4. apply iprop.

  smt().

have ->: (V - L_min  (M i) (2 ^ t1) + L_min (M i) (2 ^ t1))
   = V. smt().
rewrite Vp.
smt(@Int).
qed.   
