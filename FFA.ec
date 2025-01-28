
require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import JUtils JBigNum.

require import AuxResults. 


(* Chinese Reminder Theorem  *)
op LCM (M : int -> int) (size : int) : int.

axiom nosmt LCM_pos M n :  0 <= LCM M n.

axiom nosmt chinese_reminder_theorem x M size : 
   (forall i, 0 <= i < size => x %% M i = 0)
    <=>
    x %% LCM M size = 0.


(* big numbers, nlimb representation  *)
clone import BN as BN.

op B = Word.modulus. 
import Word.


(* summation from 0..nlimbs  *)
op sigma f = bigi predT f 0 nlimbs.

(* shorthand definitions  *)
op NativeLHS (q : int) (k_min u : int) 
                                (x y z : Word.t A.t) : int 
  = sigma (fun (i : int) => 
         sigma (fun (j : int) =>
               to_uint x.[i]  * to_uint y.[j] 
                * (B ^ (i + j) %% q)))
     - sigma (fun (i : int) => to_uint z.[i] 
         * (B ^ i %% q)) 
     - (u + k_min) * q.


op AuxLHS (q m_k v_k : int) k_min l_min u 
   (x y z : Word.t A.t) : int 
  = sigma (fun (i : int) => 
      sigma (fun (j : int) =>
              to_uint x.[i]  * to_uint y.[j] 
                 * (B ^ (i + j) %% q %% m_k)))             
     - (sigma (fun (i : int) => to_uint z.[i] 
         * (B ^ i %% q %% m_k)))
     - u * (q %% m_k)
     - (k_min * q) %% m_k
     - (v_k + l_min) * m_k.
    (* k_min * (q %% m_k)   - (k_min * q) %% m_k *)

op AuxUB (q m_k : int) k_min l_min : int 
  = (B - 1) ^ 2 * sigma (fun (i : int) => 
      sigma (fun (j : int) =>
              (B^(i + j) %% q %% m_k)))
     - (k_min * q) %% m_k
     - l_min * m_k.


op AuxLB (q m_k : int) (k_min l_min u_max v_max : int) : int 
  = (-1) * (B - 1) * 
      sigma (fun (i : int) =>
           (B ^ i  %% q  %% m_k))
     - u_max * (q %% m_k) 
     - (k_min * q) %% m_k 
     - (v_max + l_min) * m_k.


op K_min q = 
  (-1) * (((B - 1) * 
    (sigma (fun (i : int) => 
        (B ^ i) %% q))) %/ q).


op K_max (q : int) : int = 
  (B - 1) ^ 2 * 
     (sigma (fun (i : int) => 
       sigma (fun (j : int) => 
         (B ^ (i + j) %% q)))) %/ q.


op U k q = k - (K_min q). 

op L_min q m u_max = 
  (-1) * (((B - 1) * 
    (sigma (fun (i : int) => 
        (B ^ i %% q) %% m)) 
   + u_max * (q %% m) 
   + ((K_min q) * q) %% m) %/ m).


op L_max q m = 
  ((B - 1) ^ 2 * 
     (sigma (fun (i : int) => 
       sigma (fun (j : int) => 
          (B ^ (i + j) %% q %% m)))) 
   - (((K_min q) * q) %% m) ) %/ m.



lemma nosmt first_step x y : (bn x) * (bn y) 
 = sigma (fun (i : int) => 
     sigma (fun (j : int) => 
       to_uint x.[i]  * to_uint y.[j] * B ^ (i + j))).
proof. 
rewrite /sigma mulr_big /dig big_seq big_seq.
apply eq_bigr => /= i ip /=. 
rewrite big_seq big_seq.
apply eq_bigr => j /= jp /=. 
by rewrite exprD_nneg ; smt(mem_range gt0_nlimbs).
qed.


lemma nosmt upper_bound (x y :  Word.t A.t) q : 
 q <> 0 =>
    sigma (fun (i : int) => 
       sigma (fun (j : int)=> 
          to_uint x.[i] 
          * to_uint y.[j] 
          * (B ^ (i + j) %% q))) <= 
      (B - 1) ^ 2 * 
        sigma (fun (i : int) => 
          sigma (fun (j : int) => 
            (B ^ (i + j) %% q))).
move => m_not_zero.
rewrite mulr_sumr.
apply ler_sum_seq.
move => i iin _ /=.
rewrite mulr_sumr.
apply ler_sum_seq.
move => j jin _ /=.
apply kk. 
 + apply modz_ge0 => //. 
apply ler_pmul; smt(@Word). 
qed.


lemma nosmt lower_bound (x : Word.t A.t) (m : int) : m <> 0 =>
  sigma (fun (i : int) => 
     to_uint x.[i] * (B ^ i %% m))
    <= (B - 1) * sigma (fun (i : int) => 
         (B ^ i %% m)).
move => m_not_zero.   
rewrite mulr_sumr.
apply ler_sum_seq => /=.
move => i iin _.
apply ler_pmul => //.
   + smt(@Word).
   + apply modz_ge0 => //.
   + smt(@Word).
qed.   


lemma nosmt lhsub (q m_k v_k k_min l_min u : int) x y z :
       0 < m_k
    => 0 <= v_k
    => 0 <= u
    => AuxLHS q m_k v_k k_min l_min u x y z 
       <= AuxUB q m_k k_min l_min.
move => *.
rewrite /AuxLHS /AuxUB hjhjj hhelp ltr_plusc.
apply ltr_weaken.
    + apply mul_pos.
       + smt().
    + smt().
apply ltr_weaken.
     + apply mul_pos. smt().
     + apply modz_ge0 ; smt().    
apply ltr_weaken.
      + apply sumr_ge0. progress. rewrite /B.
        apply mul_pos.
        + smt(@Word).
      apply modz_ge0. smt().
rewrite mulr_sumr.
apply ler_sum_seq.
move => i iin _ /=.
rewrite mulr_sumr.
apply ler_sum_seq.
move => j jin _ /=.
apply kk.
    + apply modz_ge0 => //.  smt().
apply ler_pmul; smt(@Word).
qed.



lemma nosmt lhslb (q m_k k_min l_min u_max v_max v_k u 
 : int) x y z :
     0 < m_k 
  => v_k <= v_max
  => u <= u_max
  => AuxLB q m_k k_min l_min u_max v_max
      <= AuxLHS q m_k v_k k_min l_min u x y z.
proof.
move => *.
rewrite /AuxLB /AuxLHS 
        lhsub1 7!lhsub2.
have -> : (u_max * (q %% m_k) -
  (-1) * (B - 1) * 
   sigma (fun (i : int) => B ^ i %% q %% m_k))
    = (u_max * (q %% m_k) +
      (B - 1) * sigma (fun (i : int) => B ^ i %% q %% m_k)).
smt().    
have -> : (v_max + l_min) * m_k +
   (k_min * q %% m_k +
     (u_max * (q %% m_k) + (B - 1) 
        * sigma (fun (i : int) => B ^ i %% q %% m_k)))
    = v_max * m_k + l_min * m_k +
       k_min * q %% m_k +
        u_max * (q %% m_k) 
         + (B - 1) * sigma (fun (i : int) => 
                      B ^ i %% q %% m_k).
smt().   
have -> : (v_k + l_min) * m_k = v_k * m_k + l_min * m_k.
smt().
rewrite - 4!passoc.
apply ltr_weaken2.
      + apply mul_leq; smt().
apply ltr_weaken2 => //.
apply ltr_weaken2 => //.
apply ltr_weaken2.
      + apply mul_leq; smt().
apply ltr_weaken.
  + apply sumr_ge0. progress. apply sumr_ge0. progress.
    apply mul_pos.
      + apply mul_pos; smt(@Word).
  + smt(@Word).
rewrite mulr_sumr.
apply ler_sum_seq => /=.
move => i iin _.
apply ler_pmul; smt(@Word modz_ge0).
qed.   



lemma nosmt multiplication_soundness (M V : int -> int) 
    (M_size p q k t1 t2 : int) (x y z : Word.t A.t) : 

      (forall i,  0 < M i)

   => (NativeLHS q (K_min q) (U k q) x y z) %% p = 0

   => (forall i, 0 <= i < M_size => 
        (AuxLHS q 
            (M i) 
            (V i) 
            (K_min q) 
            (L_min q (M i) (2 ^ t1)) 
            (U k q) 
            x y z) %% p = 0)     

   =>  0 <= (U k q) < 2 ^ t1

   => (forall i,  0 <= V i < 2 ^ t2)

   => (K_max q) - (K_min q) < 2 ^ t1
        
   => (forall i, i <= 0 < M_size =>
          (L_max q (M i)) - (L_min q (M i) (2 ^ t1)) 
           < (2 ^ t2))

   => (forall i, 0 <= i < M_size => 
         (-p) < AuxLB q (M i) (K_min q) 
                  (L_min q (M i) (2 ^ t1)) 
                  (2 ^ t1) 
                  (2 ^ t2))

   => (forall i, 0 <= i < M_size => 
        AuxUB q (M i) 
                (K_min q) 
                (L_min q (M i) (2 ^ t1)) < p)
      
  => (B - 1) * (sigma (fun (i : int) => 
       (B ^ i %% q))) + (2 ^ t1 + K_min q) * q
       < LCM (fun i => if i = M_size then p else M i) 
             (M_size + 1)

  => 0 < q

  => (B - 1) ^ 2 *              
        (sigma (fun (i : int) => 
          sigma (fun (j : int) => 
            (B ^ (i + j) %% q)))) - ((K_min q) * q)
        < LCM (fun i => if i = M_size then p else M i) 
              (M_size + 1)
 
   => ((bn x) * (bn y)) %% q = (bn z) %% q.

proof.

move => H H0 H1 [H2 H3] H4 H5 H6 H7 H8 H11 H12 H13.

have H10: (B - 1) * (sigma (fun (i : int) =>
       (B ^ i %% q)))
       < LCM (fun i => if i = M_size then p else M i)
             (M_size + 1).
  + apply (add_weaken _ ((2 ^ t1 + K_min q) * q)).
     + apply mul_pos.
        + have RK1 : K_max q < 2 ^ t1 + K_min q by smt().
          have RK2 :  0 <= K_max q.
            rewrite /K_max.
            apply divz_ge0.
               smt(divz_ge0).
            apply mul_pos.
               + rewrite expr2. apply mul_pos.
                 + rewrite /B. smt(@Word).
                 rewrite /B. smt(@Word).
         apply sumr_ge0. progress.
         apply sumr_ge0. progress. smt(@Int).
     smt().
     smt().
   trivial.

have H9 : (B - 1) ^ 2 *
    (sigma (fun (i : int) =>
      sigma (fun (j : int) =>
        (B ^ (i + j) %% q)))) - k * q
      < LCM (fun i =>
             if i = M_size then p else M i)
            (M_size + 1).
  + case (0 <= k).
    + move => knn.
      apply sub_weaken ; [ smt() | trivial ].
      apply (ler_lt_trans _ _ _  _ H13) .
      apply sub_weaken2.
      apply mulnegpos.
      + rewrite /K_min.
        apply mulnegpos ; auto.
        apply divz_ge0 ; auto.
        apply mul_pos ; [ smt(@Word) | trivial ].
        apply sumr_ge0 => />.
        smt(@Int).
   smt().
   (* case k < 0  *)
  move => kn.
  have kminsk : K_min q <= k by smt().
  apply (ler_lt_trans _ _ _  _ H13).
  apply sub_weaken3 ; smt().

have R1 : (forall i, 0 <= i < M_size =>
        (AuxLHS q
            (M i)
            (V i)
            (K_min q)
            (L_min q (M i) (2 ^ t1))
            (U k q)
            x y z) = 0).
  + move => i iint.
    have R11 : AuxLHS q (M i) (V i) (K_min q)
               (L_min q (M i) (2 ^ t1))
               (U k q) x y z
      <= AuxUB q (M i) (K_min q) (L_min q (M i) (2 ^ t1)).
      + apply lhsub ; [ apply H | smt() | smt() ].
  have R12 : AuxLB q (M i) (K_min q)
              (L_min q (M i) (2 ^ t1)) (2 ^ t1) (2 ^ t2)
        <= AuxLHS q (M i) (V i) (K_min q) (L_min q (M i) (2 ^ t1)) (U k q) x y z.
    apply lhslb ; [ apply H | smt() | smt() ].
  apply (grand _ p).
    + split.
      apply (ltr_le_trans (AuxLB q (M i) (K_min q)
            (L_min q (M i) (2 ^ t1))
            (2 ^ t1) (2 ^ t2))).
        + apply H7 => //.
      apply R12.
    move => _.
    apply (ler_lt_trans (AuxUB q (M i) (K_min q)
              (L_min q (M i) (2 ^ t1)))).
      apply R11.
    apply H8 => //.
  apply H1 => //.
clear H1.

have R2 : forall (i : int),
      0 <= i && i < M_size =>
        (sigma (fun (i0 : int) =>
          sigma (fun (j : int) =>
            (to_uint x.[i0]) * (to_uint y.[j]) *
               (B ^ (i0 + j) %% q)))
        - sigma (fun (i0 : int) =>
            (to_uint z.[i0]) * (B ^ i0 %% q))
        - ((U k q) * q)
        - ((K_min q) * q)) %% (M i) = 0.
  move => i *.
  rewrite -  modzBm => /=.
  rewrite - (modzBm _ (U k q * q)).
  rewrite - modzMmr.
  rewrite - (modzBm _ (sigma (fun (i0 : int) =>
             to_uint z.[i0] * (B ^ i0 %% q)))).
  rewrite /sigma  big_mod => /=.
  rewrite {1} (big_mod _ (fun (i0 : int) =>
        to_uint z.[i0] * (B ^ i0 %% q))) => /=.
  have ->: (fun (x0 : int) =>
          to_uint z.[x0] * (B ^ x0 %% q) %% M i)
            = (fun (x0 : int) => to_uint z.[x0] *
                (B ^ x0 %% q %% M i) %% M i).
  apply fun_ext. move => x0.  by rewrite - modzMmr.
  have ->: forall (W : int),  (fun (x0 : int) =>
        bigi predT
          (fun (j : int) =>
             to_uint x.[x0]
             * to_uint y.[j]
             * (B ^ (x0 + j) %% q)) 0 nlimbs %% W)
        = (fun (x0 : int) =>
            bigi predT
             (fun (j : int) =>
                to_uint x.[x0]
                * to_uint y.[j]
                * (B ^ (x0 + j) %% q %% W))
          0 nlimbs %% W).
     move => W.
     apply fun_ext => x0.
     rewrite big_mod => /=.
     have ->: (fun (x1 : int) =>
        to_uint x.[x0]
        * to_uint y.[x1]
        * (B ^ (x0 + x1) %% q) %% W )
         = (fun (x1 : int) =>
               to_uint x.[x0]
               * to_uint y.[x1]
               * (B ^ (x0 + x1) %% q %% W) %% W).
     apply fun_ext => x1.  by rewrite - modzMmr.
      rewrite - big_mod => //.
      rewrite - big_mod => //.
      rewrite - big_mod => //.
      rewrite modzBmr.
      rewrite  modzBm  => /=.
      rewrite min_min.
   have oo: sigma (fun (i0 : int) =>
     sigma (fun (j : int) =>
          to_uint x.[i0] * to_uint y.[j] * (B ^ (i0 + j) %% q %% M i) ))
       - sigma (fun (i0 : int) => to_uint z.[i0] * (B ^ i0 %% q %% M i))
          - U k q * (q %% M i) - K_min q * q %% M i
         = (V i + L_min q (M i) (2 ^ t1)) * M i.
      have aux : AuxLHS q (M i) (V i) (K_min q)
                 (L_min q (M i) (2 ^ t1)) (U k q) x y z = 0.         apply (R1 i) => //.
         rewrite /AuxLHS in aux.
         rewrite /sigma in aux.
         rewrite - min_eq.
         apply aux.
         rewrite oo.
         apply modzMl.
clear R1.

have R3 : forall (i : int),
      0 <= i && i < M_size =>
        (sigma (fun (i0 : int) =>
          sigma (fun (j : int) =>
            (to_uint x.[i0]) * (to_uint y.[j]) *
               (B ^ (i0 + j) %% q)))
        - sigma (fun (i0 : int) =>
            (to_uint z.[i0]) * (B ^ i0 %% q))
        - k * q) %% (M i) = 0.
 + progress.
   have -> : k * q = (U k q + K_min q) * q by smt().
   have -> : (U k q + K_min q) * q
              = (U k q) * q + (K_min q) * q by smt().
   rewrite - min_min_plus. apply R2 => //.
clear R2.

pose M' := fun (i : int) => if i = M_size then p else M i.

have R4 :
    (sigma (fun (i0 : int) =>
       sigma (fun (j : int) =>
          (to_uint x.[i0]) * (to_uint y.[j]) *
              (B ^ (i0 + j) %% q)))
       - sigma (fun (i0 : int) =>
          (to_uint z.[i0]) * (B ^ i0 %% q))
        - k * q) %% (LCM M' (M_size + 1)) = 0.
  apply chinese_reminder_theorem.
  progress. rewrite /M'.
  case (i = M_size).
     move => imsize. rewrite - H0.
     rewrite /NativeLHS /B.
     have ->: (U k q + K_min q) * q = k * q by smt().
     by trivial.
  move => msize.
  apply R3. smt().
clear R3.
      
have R5 :
        (sigma (fun (i0 : int) =>
          sigma (fun (j : int) =>
            (to_uint x.[i0]) * (to_uint y.[j]) *
               (B ^ (i0 + j) %% q)))
        - sigma (fun (i0 : int) =>
            (to_uint z.[i0]) * (B ^ i0 %% q))
        - k * q) = 0.           (* bound analysis *)
  apply (grand _ (LCM M' (M_size + 1))).
  split.
  apply ltr_turnaround => //.
  rewrite neg_neg min_out_in.
  apply hjhj.
  apply (ler_lt_trans _ _ _ _ H11).
  apply add_weaken1.
  apply lower_bound.
  smt().
  apply mul_leq.
  smt().
  smt().
  split.
  apply sumr_ge0.
  progress.
  apply sumr_ge0.
  progress.
  rewrite /B.
  timeout 15. smt(@Int @Word).
  move => _.
  apply (ler_lt_trans _ _ _ _ H13).
  apply leq_sub_weak.
  apply upper_bound. smt().
  apply mulnegpos.
  rewrite /K_min.
  apply mulnegpos ; auto.
  apply divz_ge0; auto.
  apply mul_pos. smt(@Word).
  apply sumr_ge0.
  progress. smt(@Int).
  smt().
  apply LCM_pos.
  move => _.
  rewrite jkjk. apply hjhj.
  have R51 : (sigma (fun (i : int) =>
            sigma (fun (j : int)
         => to_uint x.[i]
          * to_uint y.[j]
          * (B ^ (i + j) %% q)))) - k * q
    <= (B - 1) ^ 2 *
        (sigma (fun (i : int) =>
          sigma (fun (j : int) =>
            (B ^ (i + j) %% q)))) - k * q.
     apply jjjj. apply upper_bound => //. smt().
  apply (ler_lt_trans _ _ _ R51).
  apply H9.
  split. apply sumr_ge0.
  progress. smt(@Int @Word). move => _.
  apply (ler_lt_trans _ _ _ _ H10).
  apply lower_bound => //. smt(). apply LCM_pos.
apply R4.
clear R4.

have R6 :
        (sigma (fun (i0 : int) =>
          sigma (fun (j : int) =>
            (to_uint x.[i0]) * (to_uint y.[j]) *
               (B ^ (i0 + j) %% q)))) %% q
         = sigma (fun (i0 : int) =>
            (to_uint z.[i0]) * (B ^ i0 %% q)) %% q.
move : R5.
rewrite min_min_plus.
rewrite min_eq.
move => -> .
rewrite - modzDm.
rewrite modzMl. simplify.
by apply modz_mod.
clear R5.
(* getting the final form  *)
rewrite  first_step.
rewrite /B.
rewrite /sigma.

              rewrite (big_mod _ _ nlimbs) => //. simplify.
 have -> : (fun (x0 : int) =>
     bigi predT
       (fun (j : int) => to_uint x.[x0] * to_uint y.[j] * modulus ^ (x0 + j))
       0 nlimbs %%
     q) = (fun (x0 : int) =>
     bigi predT
       (fun (j : int) => to_uint x.[x0] * to_uint y.[j] * (modulus ^ (x0 + j) %% q))
       0 nlimbs %%
     q).      apply fun_ext. move => x0.
     rewrite big_mod => /=.
     have ->: (fun (x1 : int) =>
        to_uint x.[x0] * to_uint y.[x1] * (B ^ (x0 + x1) ) %% q  )
          = (fun (x1 : int) =>
               to_uint x.[x0] * to_uint y.[x1] * (B ^ (x0 + x1) %% q) %% q ).      apply fun_ext. move => x1.  by  rewrite -  modzMmr.
      rewrite - big_mod => //.
                rewrite - big_mod => //.
rewrite /bnk /dig.
have ->: bigi predT (fun (i : int) => to_uint z.[i] * modulus ^ i) 0 nlimbs %% q
       = bigi predT (fun (i : int) => to_uint z.[i] * (modulus ^ i %% q)) 0 nlimbs %% q.
      rewrite  big_mod => //.
have ->: (fun (x0 : int) => (fun (i : int) => to_uint z.[i] * modulus ^ i) x0 %% q) = (fun (x0 : int) => (fun (i : int) => to_uint z.[i] * (modulus ^ i %% q)) x0 %% q). apply fun_ext. move => x1. by rewrite - modzMmr. simplify.
      rewrite -  big_mod => //.
apply R6.
qed.

lemma nosmt qjkj (k a b : int) : a + b = a + k + (b - k).
smt().
qed.    

lemma nosmt qjkjll (a b c : int) : a + b < c => 0 <= b => a < c.
smt().
qed.    


lemma nosmt qjkjll2 (a b c : int) : a + b < c => 0 <= a => b < c.
smt().
qed.  

lemma nosmt hlp1 (a b q : int) : a - (-1) * b * q = a + b * q.
smt().
qed.    

lemma nosmt add_pos (a b : int) : 0 <= a => 0 <= b => 0 <= a + b .
smt().
qed.    

lemma nosmt multiplication_soundness2 (M V : int -> int) 
    (M_size p q k t1 t2 : int) (x y z : Word.t A.t) : 
      (forall i,  0 < M i)

   => (NativeLHS q (K_min q) (U k q) x y z) %% p = 0

   => (forall i, 0 <= i < M_size => 
        (AuxLHS q 
            (M i) 
            (V i) 
            (K_min q) 
            (L_min q (M i) (2 ^ t1)) 
            (U k q) 
            x y z) %% p = 0)     

   =>  0 <= (U k q) < 2 ^ t1

   => (forall i,  0 <= V i < 2 ^ t2)

   => (K_max q) - (K_min q) < 2 ^ t1
        
   => (forall i, i <= 0 < M_size =>
          (L_max q (M i)) - (L_min q (M i) (2 ^ t1)) 
           < (2 ^ t2))

   => (forall i, 0 <= i < M_size => 
         (-p) < AuxLB q (M i) (K_min q) 
                  (L_min q (M i) (2 ^ t1)) 
                  (2 ^ t1) 
                  (2 ^ t2))

   => (forall i, 0 <= i < M_size => 
        AuxUB q (M i) 
                (K_min q) 
                (L_min q (M i) (2 ^ t1)) < p)
      
  => (B - 1) * (sigma (fun (i : int) => 
       (B ^ i %% q))) + (2 ^ t1) * q
     + (B - 1) ^ 2 *              
        (sigma (fun (i : int) => 
          sigma (fun (j : int) => 
            (B ^ (i + j) %% q))))
       < LCM (fun i => if i = M_size then p else M i) 
              (M_size + 1)
   => 0 < q
   => ((bn x) * (bn y)) %% q = (bn z) %% q.
proof. progress.



have boundss :  
    (B - 1) * sigma (fun (i : int) => B ^ i %% q) + 2 ^ t1 * q +
    (B - 1) ^ 2 *
    sigma (fun (i : int) => sigma (fun (j : int) => B ^ (i + j) %% q))

  = (B - 1) * (sigma (fun (i : int) => 
       (B ^ i %% q))) + (2 ^ t1 + K_min q) * q

   + (B - 1) ^ 2 *              
        (sigma (fun (i : int) => 
          sigma (fun (j : int) => 
            (B ^ (i + j) %% q)))) - (K_min q) * q.
rewrite (qjkj ((K_min q) * q)).
pose xx := (B - 1) * sigma (fun (i : int) => B ^ i %% q).      
pose yy := (B - 1) ^ 2 *
sigma (fun (i : int) => sigma (fun (j : int) => B ^ (i + j) %% q)).
smt().

have nneq : (B - 1) * (sigma (fun (i : int) => 
       (B ^ i %% q))) + (2 ^ t1 + K_min q) * q

   + ((B - 1) ^ 2 *              
        (sigma (fun (i : int) => 
          sigma (fun (j : int) => 
            (B ^ (i + j) %% q)))) - (K_min q) * q)
       < LCM (fun i => if i = M_size then p else M i) 
              (M_size + 1).
rewrite passoc.
rewrite - boundss. assumption.
clear boundss.              

have LCM_bound1 : (B - 1) * (sigma (fun (i : int) => 
       (B ^ i %% q))) + (2 ^ t1 + K_min q) * q
       < LCM (fun i => if i = M_size then p else M i) 
             (M_size + 1).
apply (qjkjll _ _ _ nneq).
rewrite /K_min.

rewrite hlp1.
apply add_pos.             
        apply mul_pos.
rewrite expr2. apply mul_pos; smt(@Word).
apply sumr_ge0 => />.
progress. apply sumr_ge0 => />. progress.
        smt(@Int).             
        apply mul_pos.
apply divz_ge0 => //.
        apply mul_pos.               
smt(@Word).
apply sumr_ge0 => />. progress.
smt(@Int). smt().             

have LCM_bound2 : (B - 1) ^ 2 *              
        (sigma (fun (i : int) => 
          sigma (fun (j : int) => 
            (B ^ (i + j) %% q)))) - ((K_min q) * q)
        < LCM (fun i => if i = M_size then p else M i) 
              (M_size + 1).
apply (qjkjll2 _ _ _ nneq).
apply add_pos.
apply mul_pos. smt(@Word).
apply sumr_ge0.
smt(@Int). apply mul_pos. 


        + have RK1 : K_max q < 2 ^ t1 + K_min q by smt().
          have RK2 :  0 <= K_max q.
            rewrite /K_max.
            apply divz_ge0.
               smt(divz_ge0).
            apply mul_pos.
               + rewrite expr2. apply mul_pos.
                 + rewrite /B. smt(@Word).
                 rewrite /B. smt(@Word).
         apply sumr_ge0. progress.
         apply sumr_ge0. progress. smt(@Int).
smt(@Int). smt().
apply (multiplication_soundness M V M_size p q k t1 t2 x y z)  => //.
qed.              
