require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract MultiScalarMul_Abstract_Setup AuxResults IterationProps.
require import Distr.
require import MultiScalarMul_Abstract_Soundness.


module UniformU : OutCalls = {
   proc getU() = {
     var u_cand;
     u_cand <$ r_distr;
     return u_cand;
   }
}.


lemma UniformU_lossless : islossless UniformU.getU.
proof. proc. rnd. skip. smt(r_distr_ll). qed.

lemma MSM_uniform_soundness P s &m :
 Pr[MultiScalarMul(UniformU).run(P, s) @ &m :
   res.`1 => res.`2 = multiScalarMul_Simpl s P T l] = 1%r.
proof. apply (MSM_soundness UniformU UniformU_lossless). qed.

(* extra assumption on the algorithm parameters  *)
axiom completeness_constraints :   forall i, 0 <= i < l
  =>  
   0 < `| (2 ^ w - 1) * (1 - i) + 2 ^ w * l | < order
  
 /\ 0 < `| (1 - 2 ^ w) * (1 + i) + 2 ^ w * l | < order.


op p1 : real = mu r_distr (fun (x : R) => x = idR).
op p2 P s : real = mu r_distr (fun (x : R) => ! u_check x P s).


lemma MSM_completeness_optimized_perfect_equiv P s &m : 
  Pr[ MultiScalarMul(UniformU).run(P,s) @&m : !res.`1 ]
   = Pr[ MultiScalarMul(UniformU).run_perfect(P,s) @&m : !res.`1 ].
byequiv (_: _ ==> res{1}.`1 = res{2}.`1).
proc.
symmetry.
ecall (complete_optimized_equiv P{1} s{1} u_cand{1}).   
call (_:true). auto. skip. smt(). auto. smt().
qed.   


lemma MSM_completeness_func_perfect_equiv P s &m :
     Pr[ MSM.multiScalarMul_Functional(P,s) @&m : !res.`1 ]
     = Pr[ MultiScalarMul(UniformU).run_perfect(P,s) @&m : !res.`1 ].
byequiv (_: _ ==> res{1}.`1 = res{2}.`1).
proc.
inline UniformU.getU.
seq 1 1 : (#pre /\ u_cand{1} = u_cand0{2}).
    rnd. skip. progress.
inline MSM.completeMain.
wp.
 exists* P{2}, s{2} , u_cand0{2}. elim*. move => argP argS argU.
call {2} (completeMainLoop_spec_ph2 argP argS argU T). smt(param_pos).
wp. skip. progress. auto. smt().
qed.


lemma MSM_loop_failure_bound argP args :
 mu r_distr (fun u =>
  !(multiScalarMulLoop T l (perfect_table_pure argP u) args (l *** u) w).`1)
 <= T%r * (l%r * (p1 + p1)).
proof.
rewrite /multiScalarMulLoop.
  have -> : (fun (x : R) =>
     ! (iteri T
          (fun (i : int) (acc : bool * R) =>
             let r =
               completeAddLoop l (perfect_table_pure argP x) args i
                 (2 ^ w *** acc.`2) in (acc.`1 /\ r.`1, r.`2))
          (true, l *** x)).`1)
     = (fun (x : R) =>
     ! (iteri T
          (fun (i : int) (acc : bool * R) =>
             let myacc = gg args argP i x in
             let r =
               completeAddLoop l (perfect_table_pure argP x) args i
                 (2 ^ w *** myacc ) in (acc.`1 /\ r.`1, r.`2))
          (true, l *** x)).`1).
apply fun_ext. move => x.
 rewrite   (iteriG (fun (x : bool * R) => x.`1) (fun (x : bool * R) => x.`2)
   (fun (i : int) (acc1 : bool ) (acc2 : R) =>
         let r =
           completeAddLoop l (perfect_table_pure argP x) args i
             (2 ^ w *** acc2) in (acc1 /\ r.`1, r.`2)) T _ (true, l *** x)  ).
smt(param_pos). simplify.
  pose f1 := (fun (i : int) (acc : bool * R) =>
         (acc.`1 /\
          (completeAddLoop l (perfect_table_pure argP x) args i
             (2 ^ w ***
              (iteri i
                 (fun (i0 : int) (acc0 : bool * R) =>
                    (acc0.`1 /\
                     (completeAddLoop l (perfect_table_pure argP x) args
                        i0 (2 ^ w *** acc0.`2)).`1,
                     (completeAddLoop l (perfect_table_pure argP x) args
                        i0 (2 ^ w *** acc0.`2)).`2)) (true, l *** x)).`2)).`1,
          (completeAddLoop l (perfect_table_pure argP x) args i
             (2 ^ w ***
              (iteri i
                 (fun (i0 : int) (acc0 : bool * R) =>
                    (acc0.`1 /\
                     (completeAddLoop l (perfect_table_pure argP x) args
                        i0 (2 ^ w *** acc0.`2)).`1,
                     (completeAddLoop l (perfect_table_pure argP x) args
                        i0 (2 ^ w *** acc0.`2)).`2)) (true, l *** x)).`2)).`2)).
   pose f2 :=       (fun (i : int) (acc : bool * R) =>
        (acc.`1 /\
         (completeAddLoop l (perfect_table_pure argP x) args i
            (2 ^ w *** (gg args argP i x))).`1,
         (completeAddLoop l (perfect_table_pure argP x) args i
            (2 ^ w *** (gg args argP i x))).`2)).
 rewrite (eq_iteri f1 f2 T _ _).
progress.
 (* apply fun_ext. move => z. apply fun_ext. move => zz. progress. *)
rewrite /f1 /f2.      
        have -> : (iteri i
        (fun (i0 : int) (acc0 : bool * R) =>
           (acc0.`1 /\
            (completeAddLoop l (perfect_table_pure argP x) args i0
               (2 ^ w *** acc0.`2)).`1,
            (completeAddLoop l (perfect_table_pure argP x) args i0
               (2 ^ w *** acc0.`2)).`2)) (true, l *** x)).`2 = gg args argP i x.
rewrite (spec_equiv_fun_impl i args x argP).  auto.
      auto. auto. auto.
apply (iteri_ub3 (fun (x : R) => l *** x)   
        (fun x i => completeAddLoop l (perfect_table_pure argP x) args i
               (2 ^ w *** (gg args argP i x) )) r_distr T (l%r * (p1 + p1)) _ ). smt(param_pos).
simplify.
move => i.
rewrite /completeAddLoop. simplify.            
have -> : (fun (r : R) =>
     ! (iteri l
          (fun (j : int) (acc : bool * R) =>
             (acc.`1 /\
              xdiff acc.`2 (perfect_table_pure argP r j (args j i)),
              acc.`2 +++ perfect_table_pure argP r j (args j i)))
          (true, 2 ^ w *** (gg args argP i r))).`1)
      =
      (fun (r : R) =>
     ! (iteri l
          (fun (j : int) (acc : bool * R) =>
             (acc.`1 /\
              xdiff (hh args argP i j r) (perfect_table_pure argP r j (args j i)),
              (hh args argP i j r) +++ perfect_table_pure argP r j (args j i)))
          (true, 2 ^ w *** (gg args argP i r))).`1).
apply fun_ext. move => r.
 rewrite   (iteriG (fun (x : bool * R) => x.`1) (fun (x : bool * R) => x.`2)
   (fun (j : int) (acc1 : bool) (acc2 : R) =>
        (acc1 /\ xdiff acc2 (perfect_table_pure argP r j (args j i)),
         acc2 +++ perfect_table_pure argP r j (args j i))) l _ (true, 2 ^ w *** gg args argP i r)  ). smt(param_pos). simplify.

 pose f1 := (fun (i0 : int) (acc : bool * R) =>
         (acc.`1 /\
          xdiff
            (iteri i0
               (fun (i1 : int) (acc0 : bool * R) =>
                  (acc0.`1 /\
                   xdiff acc0.`2 (perfect_table_pure argP r i1 (args i1 i)),
                   acc0.`2 +++ perfect_table_pure argP r i1 (args i1 i)))
               (true, 2 ^ w *** gg args argP i r)).`2
            (perfect_table_pure argP r i0 (args i0 i)),
          (iteri i0
             (fun (i1 : int) (acc0 : bool * R) =>
                (acc0.`1 /\
                 xdiff acc0.`2 (perfect_table_pure argP r i1 (args i1 i)),
                 acc0.`2 +++ perfect_table_pure argP r i1 (args i1 i)))
             (true, 2 ^ w *** gg args argP i r)).`2 +++
          perfect_table_pure argP r i0 (args i0 i))).

  pose f2 := (fun (j : int) (acc : bool * R) =>
        (acc.`1 /\ xdiff (hh args argP i j r) (perfect_table_pure argP r j (args j i)),
         (hh args argP i j r) +++ perfect_table_pure argP r j (args j i))).
     
 rewrite (eq_iteri f1 f2 l _ _).
progress. rewrite /f1 /f2.

 have -> : (iteri i0
    (fun (i1 : int) (acc0 : bool * R) =>
       (acc0.`1 /\ xdiff acc0.`2 (perfect_table_pure argP r i1 (args i1 i)),
        acc0.`2 +++ perfect_table_pure argP r i1 (args i1 i)))
    (true, 2 ^ w *** gg args argP i r)).`2
   =  (hh args argP i i0 r) .
rewrite comeqsimp. auto.
auto. auto. auto.
move => condi.
apply  (iteri_ub3 (fun (x : R) => 2 ^ w *** (gg args argP i x))
   (fun r j => (xdiff (hh args argP i j r) (perfect_table_pure argP r j (args j i)) , (hh args argP i j r) +++ perfect_table_pure argP r j (args j i))  )
   r_distr l (p1 + p1) _). smt(param_pos).
progress.

have oo : (fun (r : R) =>
     ! xdiff (hh args argP i i0 r)
         (perfect_table_pure argP r i0 (args i0 i)))
       <= (fun (r : R) =>
        ((hh args argP i i0 r) =
         (perfect_table_pure argP r i0 (args i0 i))
           \/         (hh args argP i i0 r) =
         (- perfect_table_pure argP r i0 (args i0 i)))).

move => r. progress.
     apply notxdiff. auto.
  apply (RealOrder.ler_trans  
           (mu r_distr
    (fun (r : R) =>
        ((hh args argP i i0 r) =
         (perfect_table_pure argP r i0 (args i0 i))
           \/         (hh args argP i i0 r) =
         (- perfect_table_pure argP r i0 (args i0 i))))
   )).
rewrite (mu_sub r_distr _ _ oo).       

apply mu_or_leq_param.
rewrite /hh. rewrite /perfect_table_pure. rewrite /gg.

have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR =
     args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x)

   = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l +++ l *** x) +++
     (iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR)
     +++  - (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x) = idR).
apply fun_ext. move => r. smt(const_add_inj op_inv).
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR +++
     - (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x) = idR)
 = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR +++
     - (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x)  = idR).
     apply fun_ext. move => r.
smt.
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR +++
     - (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x)  = idR)
  = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j)) idR +++ i0 *** - (2 ^ w - 1) *** x +++
     - (args i0 i *** argP i0) +++ (2 ^ w - 1) *** x  = idR).
     apply fun_ext. move => r.
       pose k := 2 ^ w *** multiScalarMul_Simpl args argP i l +++ 2 ^ w *** (l *** r).

 
     rewrite  (iteriZZZZ (fun j => args j i *** argP j) i0 _ (- (2 ^ w - 1) *** r)) . smt(). simplify. rewrite op_neg_add neg_neg_id. smt(op_assoc).
 

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++ 2 ^ w *** (l *** x) +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     i0 *** - (2 ^ w - 1) *** x +++ - args i0 i *** argP i0 +++
     (2 ^ w - 1) *** x = idR)
   = (fun (x : R) =>
     (2 ^ w *** multiScalarMul_Simpl args argP i l  +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR     +++ - args i0 i *** argP i0) +++

     ((2 ^ w - 1) *** x +++
     i0 *** - (2 ^ w - 1) *** x  +++
     2 ^ w *** (l *** x)) = idR).
apply fun_ext. move => r. smt(op_assoc op_comm).

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     - args i0 i *** argP i0 +++
     ((2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) =
     idR)
     =  (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     - args i0 i *** argP i0 +++ x = idR) \o (fun  x => ((2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) ). smt().
     rewrite - dmapE. simplify.

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     - args i0 i *** argP i0 +++ x = idR)
     = (fun x => x = idR) \o (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     - args i0 i *** argP i0 +++ x). smt().
     rewrite - dmapE.

have ->: (dmap r_distr
        (fun (x : R) =>
           (2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
           2 ^ w *** (l *** x))) = r_distr. 
     have ->: (fun (x : R) =>
     (2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++ 2 ^ w *** (l *** x))
    = (fun (x : R) =>
     ((2 ^ w - 1) +  i0 * - (2 ^ w - 1)  + 2 ^ w * l) *** x).
       apply fun_ext. move => x.
       rewrite - neg_mul.
       rewrite - nmul_mul.
       rewrite  - nplus_dist.
       rewrite - nmul_mul.
       rewrite  - nplus_dist.
       auto.
apply (dmap_bij r_distr r_distr _ (fun (x : R) => (invertme (2 ^ w - 1 + i0 * - (2 ^ w - 1) + 2 ^ w * l) ) *** x ) ).
progress. apply r_distr_full.
progress. apply r_distr_funi.          
  progress. 
pose A := 2 ^ w - 1.
have -> : (A + i0 * -A + 2 ^ w * l) = (A + - i0 * A + 2 ^ w * l). smt().
have ->: (A + - i0 * A + 2 ^ w * l) = A * (1 - i0) + 2 ^ w * l. smt().
   
rewrite invertmeP. rewrite /A. smt(completeness_constraints). auto. 

progress. 
pose A := 2 ^ w - 1.
have -> : (A + i0 * -A + 2 ^ w * l) = (A + - i0 * A + 2 ^ w * l). smt().
have ->: (A + - i0 * A + 2 ^ w * l) = A * (1 - i0) + 2 ^ w * l. smt().
timeout 10.
have ->: (A * (1 - i0) + 2 ^ w * l) *** (invertme (A * (1 - i0) + 2 ^ w * l) *** b)
 =  invertme (A * (1 - i0) + 2 ^ w * l) *** ((A * (1 - i0) + 2 ^ w * l)  *** b).
 smt.
rewrite invertmeP. rewrite /A. smt(completeness_constraints). auto. 

   
have ->: (dmap r_distr
     (fun (x : R) =>
        2 ^ w *** multiScalarMul_Simpl args argP i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j)
          idR +++
        - args i0 i *** argP i0 +++ x))
   = r_distr.
apply (dmap_bij r_distr r_distr _ (fun (x : R) =>   -  (2 ^ w *** multiScalarMul_Simpl args argP i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j)
          idR +++
        - args i0 i *** argP i0)  +++ x )).
progress. apply r_distr_full.
progress. apply r_distr_funi.
progress. apply op_cancel_left.
progress. apply op_cancel_right.
auto.
(* second symmetrical case *)
rewrite /hh. rewrite /perfect_table_pure. rewrite /gg.

have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR =
     - (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x))

   = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l +++ l *** x) +++
     (iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR)
     +++  (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x) = idR).
apply fun_ext. move => r. apply op_eq_neg.
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR +++
      (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x) = idR)
 = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR +++
      (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x)  = idR).
     apply fun_ext. move => r.
smt.
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j +++ - (2 ^ w - 1) *** x)) idR +++
      (args i0 i *** argP i0 +++ - (2 ^ w - 1) *** x)  = idR)
  = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl args argP i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (args j i *** argP j)) idR +++ i0 *** - (2 ^ w - 1) *** x +++
     (args i0 i *** argP i0) +++  - (2 ^ w - 1) *** x  = idR).
     apply fun_ext. move => r.
       pose k := 2 ^ w *** multiScalarMul_Simpl args argP i l +++ 2 ^ w *** (l *** r).

 
     rewrite  (iteriZZZZ (fun j => args j i *** argP j) i0 _ (- (2 ^ w - 1) *** r)) . smt(). smt(op_assoc op_comm).

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++ 2 ^ w *** (l *** x) +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     i0 *** - (2 ^ w - 1) *** x +++ args i0 i *** argP i0 +++
     - (2 ^ w - 1) *** x = idR)
   = (fun (x : R) =>
     (2 ^ w *** multiScalarMul_Simpl args argP i l  +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR     +++  args i0 i *** argP i0) +++

     (- (2 ^ w - 1) *** x +++
     i0 *** - (2 ^ w - 1) *** x  +++
     2 ^ w *** (l *** x)) = idR).
apply fun_ext. move => r. smt(op_assoc op_comm).

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
      args i0 i *** argP i0 +++
     (- (2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) =
     idR)
     =  (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     args i0 i *** argP i0 +++ x = idR) \o (fun  x => (-(2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) ). smt().
     rewrite - dmapE. simplify.

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
     args i0 i *** argP i0 +++ x = idR)
     = (fun x => x = idR) \o (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl args argP i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j) idR +++
      args i0 i *** argP i0 +++ x). smt().
     rewrite - dmapE.

have ->: (dmap r_distr
        (fun (x : R) =>
           - (2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
           2 ^ w *** (l *** x))) = r_distr. 
     have ->: (fun (x : R) =>
     - (2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++ 2 ^ w *** (l *** x))
    = (fun (x : R) =>
     (- (2 ^ w - 1) +  i0 * - (2 ^ w - 1)  + 2 ^ w * l) *** x).
       apply fun_ext. move => x.
       rewrite - neg_mul.
       rewrite - nmul_mul.
       rewrite  - nplus_dist.
       rewrite - nmul_mul.
       rewrite  - nplus_dist.
       auto.
apply (dmap_bij r_distr r_distr _ (fun (x : R) => (invertme (- (2 ^ w - 1) + i0 * - (2 ^ w - 1) + 2 ^ w * l) ) *** x ) ).
progress. apply r_distr_full.
progress. apply r_distr_funi.          
  progress. rewrite invertmeP.
smt(completeness_constraints).   
auto.

progress.
 have ->: ((- (2 ^ w - 1)) + i0 * - (2 ^ w - 1) + 2 ^ w * l) ***
(invertme ((- (2 ^ w - 1)) + i0 * - (2 ^ w - 1) + 2 ^ w * l) *** b)
  = (invertme ((- (2 ^ w - 1)) + i0 * - (2 ^ w - 1) + 2 ^ w * l)) ***
( ((- (2 ^ w - 1)) + i0 * - (2 ^ w - 1) + 2 ^ w * l) *** b). smt.   
rewrite invertmeP.
smt(completeness_constraints).    auto.
  
have ->: (dmap r_distr
     (fun (x : R) =>
        2 ^ w *** multiScalarMul_Simpl args argP i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j)
          idR +++
        args i0 i *** argP i0 +++ x))
   = r_distr.
apply (dmap_bij r_distr r_distr _ (fun (x : R) =>   -  (2 ^ w *** multiScalarMul_Simpl args argP i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ args j i *** argP j)
          idR +++
         args i0 i *** argP i0)  +++ x )).
progress. apply r_distr_full.
progress. apply r_distr_funi.
progress. apply op_cancel_left.
progress. apply op_cancel_right.
auto.
qed.

lemma MSM_completeness_functional argP args :
  phoare [ MSM.multiScalarMul_Functional :
      arg = (argP , args) ==> !res.`1 ]
            <= ((p2 argP args) + (T%r * (l%r * (p1 + p1)))).
proc.
wp. rnd. skip. progress.
simplify.
rewrite mu_split. simplify.
apply mu_split_q.
apply kkkk. smt().
auto.
apply MSM_loop_failure_bound.
progress. rewrite /p1 /p2. smt(ge0_mu param_pos).
qed.


lemma MSM_completeness argP args &m : 
  Pr[ MultiScalarMul(UniformU).run(argP,args) @&m : !res.`1 ]
       <= ((p2 argP args) + T%r * (l%r * (p1 + p1))).
rewrite MSM_completeness_optimized_perfect_equiv.
rewrite - MSM_completeness_func_perfect_equiv.
byphoare (_: arg = (argP , args) ==> _).
apply MSM_completeness_functional. auto. auto.
qed.  


(* Normalization makes returned success complementary to returned failure. *)
lemma MSM_uniform_lossless : islossless MultiScalarMul(UniformU).run.
proof.
proc.
ecall (MSM_soundness_param_u_ph UniformU UniformU_lossless P s u_cand); call UniformU_lossless; auto.
qed.

lemma MSM_uniform_success P s &m :
 1%r - (p2 P s + T%r * (l%r * (p1 + p1)))
 <= Pr[MultiScalarMul(UniformU).run(P,s) @ &m : res.`1].
proof.
have Hfail := MSM_completeness P s &m.
have Htotal : Pr[MultiScalarMul(UniformU).run(P,s) @ &m : true] = 1%r
 by byphoare MSM_uniform_lossless.
move: Hfail. rewrite Pr [mu_not] Htotal.
smt().
qed.
