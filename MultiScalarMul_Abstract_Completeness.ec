require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.


require import MultiScalarMul_Abstract MultiScalarMul_Abstract_Setup AuxResults IterationProps.
require import Distr.


op p1 : real = mu r_distr (fun (x : R) => x = idR).
op p2 P s : real = mu r_distr (fun (x : R) => ! u_check x P s).



lemma incompleteAddLoop_specR_ph argcc argT argic args  :
 phoare [ SimpleComp.incompleteAddLoop : arg = (argcc, argT, argic,  args)
     ==>  res = incompleteAddLoop l argT args argic argcc ] = 1%r.
proc.
while (0 <= jc 
 /\ jc <= l 
 /\ flag = (iteri 
                  jc 
                  (fun j (acc : bool * R) => 
                     (acc.`1 /\ xdiff acc.`2 (argT j (args j argic)) , 
                      acc.`2 %%% argT j (args j argic))) 
                  (true, argcc)).`1
 /\ (acc, table, ic,  s) = (argcc, argT, argic, args) 
 /\ vahe =  (iteri jc (fun j (acc : bool * R) => (acc.`1 /\ xdiff acc.`2 (argT j (args j argic)) , acc.`2 %%% argT j (args j argic))) (true, argcc)).`2) (l - jc).
move => z.
wp. skip. progress. smt(). smt(). rewrite iteriS. smt().
   simplify.
   rewrite /xdiff. 
pose xxx := (iteri jc{hr}
     (fun (j : int) (acc0 : bool * R) =>
        (acc0.`1 /\
         xof acc0.`2 <> xof (table{hr} j (s{hr} j ic{hr})) && acc0.`2 <> idR,
         acc0.`2 %%% table{hr} j (s{hr} j ic{hr}))) (true, acc{hr})).
pose yyy := (iteri jc{hr}
       (fun (j : int) (acc0 : R) => acc0 %%% table{hr} j (s{hr} j ic{hr}))
       acc{hr}).     smt().
rewrite iteriS. smt().
smt(op_assoc).
smt().   
   wp. skip. progress. smt(l_pos). 
rewrite iteri0. auto. auto.
rewrite iteri0. auto. auto.
smt().   
smt().
qed.  



lemma incompleteAddLoop_specR_h argcc argT argic args  :
 hoare [ SimpleComp.incompleteAddLoop : arg = (argcc, argT, argic,  args)
     ==>  res = incompleteAddLoop l argT args argic argcc ].
conseq (incompleteAddLoop_specR_ph argcc argT argic args).
qed.   


lemma multm_spec_h argP args argU  :
 hoare [ SimpleComp.multiScalarMulMain_Opt : arg = (argP, args, argU)   
  ==>  res = multiScalarMul T l (perfect_table_pure argP argU) args (l *** argU) w   ] .
proc. 
while (
  0 <= ic 
  /\ ic <= T
  /\ (U, table, s) = (argU, (perfect_table_pure argP argU), args) 
  /\ (flag , acc) = multiScalarMul ic l ((perfect_table_pure argP argU)) args (l *** argU) w
 ) .

wp.
ecall (incompleteAddLoop_specR_h acc (perfect_table_pure argP argU) ic args).
ecall (doublewtimes_spec acc w). 
skip.
progress. smt(w_pos).
smt(). smt().
rewrite /multiScalarMul.
rewrite iteriS. smt().
smt().
wp. skip. progress. smt(T_pos).   
rewrite /multiScalarMul. rewrite iteri0.
auto. auto. 
have -> : T = ic0. smt(T_pos).
rewrite - H2.
 smt().
qed. 


lemma multm_spec_ph argP args argU  :
 phoare [ SimpleComp.multiScalarMulMain_Opt : arg = (argP, args, argU)   
  ==>  res = multiScalarMul T l (perfect_table_pure argP argU) args (l *** argU) w ]  = 1%r.
phoare split ! 1%r 0%r. auto.
   proc. wp.
while (table = (perfect_table_pure argP argU) /\ s = args) (T - ic). progress.
wp.
exists* acc, table, ic, s.
elim*. move => accV tableV icV sV.
call (incompleteAddLoop_specR_ph (2 ^ w *** accV) (perfect_table_pure argP argU) icV args).
call (doublewtimes_spec_ph accV MultiScalarMul_Abstract.w).
skip.  progress. smt(w_pos).  smt().
wp. progress.
auto. smt(). hoare.
apply multm_spec_h. 
qed.



lemma compl_I_equiv : 
 equiv [ SimpleComp.multiScalarMul_Fun ~
         MultiScalarMul(UniformU).run
     : ={arg} ==> res{1}.`1 = res{2}.`1 ].
proc.
inline UniformU.getU. 

seq 1 1 : (#pre /\ u_cand{1} = u_cand0{2}).
    rnd. skip. progress.
inline SimpleComp.multiScalarMulMain_Opt_Corrected.
wp.    
ecall {2} (multm_spec_ph P{2} s{2} u_cand{2}).
wp. skip. progress.   
qed.


lemma compl_flags P s &m : 
  Pr[ MultiScalarMul(UniformU).run(P,s) @&m : !res.`1 ]
   = Pr[ MultiScalarMul(UniformU).run_perfect(P,s) @&m : !res.`1 ].
byequiv (_: _ ==> res{1}.`1 = res{2}.`1).
proc.
symmetry.
ecall (multieqs2 P{1} s{1} u_cand{1}).   
call (_:true). auto. skip. smt(). auto. smt().
qed.   


lemma compl_II_equiv P s &m :
     Pr[ SimpleComp.multiScalarMul_Fun2(P,s) @&m : !res.`1 ]
     = Pr[ MultiScalarMul(UniformU).run_perfect(P,s) @&m : !res.`1 ].
byequiv (_: _ ==> res{1}.`1 = res{2}.`1).
proc.
inline UniformU.getU.
seq 1 1 : (#pre /\ u_cand{1} = u_cand0{2}).
    rnd. skip. progress.
inline SimpleComp.multiScalarMulMain_Perfect.
wp.
 exists* P{2}, s{2} , u_cand0{2}. elim*. move => argP argS argU.
call {2} (multm_spec_ph2 argP argS argU T). smt(T_pos).
wp. skip. progress. auto. smt().
qed.


lemma completeness_I argP args :
  phoare [ SimpleComp.multiScalarMul_Fun2 :
      arg = (argP , args) ==> !res.`1 ] 
            <= ((p2 argP args) + (T%r * (l%r * (p1 + p1)))).
proc.
wp. rnd. skip. progress. 
pose f := fun a i b => 
  (completeAddLoop l (perfect_table_pure P{hr} a)
    s{hr} i (2 ^ w *** b)).
simplify.
rewrite mu_split. simplify.
apply mu_split_q.
apply kkkk. smt().
auto.
rewrite /multiScalarMul_Complete.

  have -> : (fun (x : R) =>
     ! (iteri T
          (fun (i : int) (acc : bool * R) =>
             let r =
               completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
                 (2 ^ w *** acc.`2) in (acc.`1 /\ r.`1, r.`2))
          (true, l *** x)).`1)
     = (fun (x : R) =>
     ! (iteri T
          (fun (i : int) (acc : bool * R) =>
             let myacc = gg s{hr} P{hr} i x in
             let r =
               completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
                 (2 ^ w *** myacc ) in (acc.`1 /\ r.`1, r.`2))
          (true, l *** x)).`1).
apply fun_ext. move => x.



 rewrite   (iteriG (fun (x : bool * R) => x.`1) (fun (x : bool * R) => x.`2)
   (fun (i : int) (acc1 : bool ) (acc2 : R) =>
         let r =
           completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
             (2 ^ w *** acc2) in (acc1 /\ r.`1, r.`2)) T _ (true, l *** x)  ).
smt(T_pos). simplify.

  pose f1 := (fun (i : int) (acc : bool * R) =>
         (acc.`1 /\
          (completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
             (2 ^ w ***
              (iteri i
                 (fun (i0 : int) (acc0 : bool * R) =>
                    (acc0.`1 /\
                     (completeAddLoop l (perfect_table_pure P{hr} x) s{hr}
                        i0 (2 ^ w *** acc0.`2)).`1,
                     (completeAddLoop l (perfect_table_pure P{hr} x) s{hr}
                        i0 (2 ^ w *** acc0.`2)).`2)) (true, l *** x)).`2)).`1,
          (completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
             (2 ^ w ***
              (iteri i
                 (fun (i0 : int) (acc0 : bool * R) =>
                    (acc0.`1 /\
                     (completeAddLoop l (perfect_table_pure P{hr} x) s{hr}
                        i0 (2 ^ w *** acc0.`2)).`1,
                     (completeAddLoop l (perfect_table_pure P{hr} x) s{hr}
                        i0 (2 ^ w *** acc0.`2)).`2)) (true, l *** x)).`2)).`2)).
   pose f2 :=       (fun (i : int) (acc : bool * R) =>
        (acc.`1 /\
         (completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
            (2 ^ w *** (gg s{hr} P{hr} i x))).`1,
         (completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
            (2 ^ w *** (gg s{hr} P{hr} i x))).`2)).

 rewrite (eq_iteri f1 f2 T _ _).

progress.
 (* apply fun_ext. move => z. apply fun_ext. move => zz. progress. *)
rewrite /f1 /f2.      
        have -> : (iteri i
        (fun (i0 : int) (acc0 : bool * R) =>
           (acc0.`1 /\
            (completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i0
               (2 ^ w *** acc0.`2)).`1,
            (completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i0
               (2 ^ w *** acc0.`2)).`2)) (true, l *** x)).`2 = gg s{hr} P{hr} i x. 
rewrite (muleqsimp2 i s{hr} x P{hr}).  auto.

      auto. auto. auto.
apply (iteri_ub3 (fun (x : R) => l *** x)   
        (fun x i => completeAddLoop l (perfect_table_pure P{hr} x) s{hr} i
               (2 ^ w *** (gg s{hr} P{hr} i x) )) r_distr T (l%r * (p1 + p1)) _ ).  
simplify.
move => i.
rewrite /completeAddLoop. simplify.
             
have -> : (fun (r : R) =>
     ! (iteri l
          (fun (j : int) (acc : bool * R) =>
             (acc.`1 /\
              xdiff acc.`2 (perfect_table_pure P{hr} r j (s{hr} j i)),
              acc.`2 +++ perfect_table_pure P{hr} r j (s{hr} j i)))
          (true, 2 ^ w *** (gg s{hr} P{hr} i r))).`1)

      =

      (fun (r : R) =>
     ! (iteri l
          (fun (j : int) (acc : bool * R) =>
             (acc.`1 /\
              xdiff (hh s{hr} P{hr} i j r) (perfect_table_pure P{hr} r j (s{hr} j i)),

              (hh s{hr} P{hr} i j r) +++ perfect_table_pure P{hr} r j (s{hr} j i)))
          (true, 2 ^ w *** (gg s{hr} P{hr} i r))).`1).
apply fun_ext. move => r.

 rewrite   (iteriG (fun (x : bool * R) => x.`1) (fun (x : bool * R) => x.`2)
   (fun (j : int) (acc1 : bool) (acc2 : R) =>
        (acc1 /\ xdiff acc2 (perfect_table_pure P{hr} r j (s{hr} j i)),
         acc2 +++ perfect_table_pure P{hr} r j (s{hr} j i))) l _ (true, 2 ^ w *** gg s{hr} P{hr} i r)  ). smt(l_pos). simplify. 

 pose f1 := (fun (i0 : int) (acc : bool * R) =>
         (acc.`1 /\
          xdiff
            (iteri i0
               (fun (i1 : int) (acc0 : bool * R) =>
                  (acc0.`1 /\
                   xdiff acc0.`2 (perfect_table_pure P{hr} r i1 (s{hr} i1 i)),
                   acc0.`2 +++ perfect_table_pure P{hr} r i1 (s{hr} i1 i)))
               (true, 2 ^ w *** gg s{hr} P{hr} i r)).`2
            (perfect_table_pure P{hr} r i0 (s{hr} i0 i)),
          (iteri i0
             (fun (i1 : int) (acc0 : bool * R) =>
                (acc0.`1 /\
                 xdiff acc0.`2 (perfect_table_pure P{hr} r i1 (s{hr} i1 i)),
                 acc0.`2 +++ perfect_table_pure P{hr} r i1 (s{hr} i1 i)))
             (true, 2 ^ w *** gg s{hr} P{hr} i r)).`2 +++
          perfect_table_pure P{hr} r i0 (s{hr} i0 i))).

  pose f2 := (fun (j : int) (acc : bool * R) =>
        (acc.`1 /\ xdiff (hh s{hr} P{hr} i j r) (perfect_table_pure P{hr} r j (s{hr} j i)),
         (hh s{hr} P{hr} i j r) +++ perfect_table_pure P{hr} r j (s{hr} j i))).
     
 rewrite (eq_iteri f1 f2 l _ _).
progress. rewrite /f1 /f2.

 have -> : (iteri i0
    (fun (i1 : int) (acc0 : bool * R) =>
       (acc0.`1 /\ xdiff acc0.`2 (perfect_table_pure P{hr} r i1 (s{hr} i1 i)),
        acc0.`2 +++ perfect_table_pure P{hr} r i1 (s{hr} i1 i)))
    (true, 2 ^ w *** gg s{hr} P{hr} i r)).`2
   =  (hh s{hr} P{hr} i i0 r) .
rewrite comeqsimp. auto.
auto. auto. auto.
move => condi.
apply  (iteri_ub3 (fun (x : R) => 2 ^ w *** (gg s{hr} P{hr} i x)) 
   (fun r j => (xdiff (hh s{hr} P{hr} i j r) (perfect_table_pure P{hr} r j (s{hr} j i)) , (hh s{hr} P{hr} i j r) +++ perfect_table_pure P{hr} r j (s{hr} j i))  )
   r_distr l (p1 + p1) _).  
progress.

have oo : (fun (r : R) =>
     ! xdiff (hh s{hr} P{hr} i i0 r)
         (perfect_table_pure P{hr} r i0 (s{hr} i0 i)))
       <= (fun (r : R) =>
        ((hh s{hr} P{hr} i i0 r) =
         (perfect_table_pure P{hr} r i0 (s{hr} i0 i)) 
           \/         (hh s{hr} P{hr} i i0 r) =
         (- perfect_table_pure P{hr} r i0 (s{hr} i0 i)))).

move => r. progress.
     apply notxdiff. auto.
  apply (RealOrder.ler_trans  
           (mu r_distr
    (fun (r : R) =>
        ((hh s{hr} P{hr} i i0 r) =
         (perfect_table_pure P{hr} r i0 (s{hr} i0 i)) 
           \/         (hh s{hr} P{hr} i i0 r) =
         (- perfect_table_pure P{hr} r i0 (s{hr} i0 i))))
   )).
rewrite (mu_sub r_distr _ _ oo).       

apply mu_or_leq_param.
rewrite /hh. rewrite /perfect_table_pure. rewrite /gg.

have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR =
     s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x)

   = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l +++ l *** x) +++
     (iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR)
     +++  - (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x) = idR).
apply fun_ext. move => r. timeout 10. smt.
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR +++
     - (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x) = idR)
 = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR +++
     - (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x)  = idR).
     apply fun_ext. move => r.
smt.
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR +++
     - (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x)  = idR)
  = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j)) idR +++ i0 *** - (2 ^ w - 1) *** x +++
     - (s{hr} i0 i *** P{hr} i0) +++ (2 ^ w - 1) *** x  = idR).
     apply fun_ext. move => r.
       pose k := 2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++ 2 ^ w *** (l *** r).

 
     rewrite  (iteriZZZZ (fun j => s{hr} j i *** P{hr} j) i0 _ (- (2 ^ w - 1) *** r)) . smt(). timeout 10. smt.
 

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++ 2 ^ w *** (l *** x) +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     i0 *** - (2 ^ w - 1) *** x +++ - s{hr} i0 i *** P{hr} i0 +++
     (2 ^ w - 1) *** x = idR)
   = (fun (x : R) =>
     (2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l  +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR     +++ - s{hr} i0 i *** P{hr} i0) +++

     ((2 ^ w - 1) *** x +++
     i0 *** - (2 ^ w - 1) *** x  +++
     2 ^ w *** (l *** x)) = idR).
apply fun_ext. move => r. timeout 10. smt.

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     - s{hr} i0 i *** P{hr} i0 +++
     ((2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) =
     idR)
     =  (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     - s{hr} i0 i *** P{hr} i0 +++ x = idR) \o (fun  x => ((2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) ). smt().
     rewrite - dmapE. simplify.

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     - s{hr} i0 i *** P{hr} i0 +++ x = idR)
     = (fun x => x = idR) \o (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     - s{hr} i0 i *** P{hr} i0 +++ x). smt().
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
  progress. rewrite invertmeP. auto.

progress. smt. 
   
have ->: (dmap r_distr
     (fun (x : R) =>
        2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j)
          idR +++
        - s{hr} i0 i *** P{hr} i0 +++ x))
   = r_distr.
apply (dmap_bij r_distr r_distr _ (fun (x : R) =>   -  (2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j)
          idR +++
        - s{hr} i0 i *** P{hr} i0)  +++ x )).
progress. apply r_distr_full.
progress. apply r_distr_funi.
progress. timeout 10. smt.
progress. timeout 10. smt.
auto.








(* second symmetrical case *)



rewrite /hh. rewrite /perfect_table_pure. rewrite /gg.

have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR =
     - (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x))

   = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l +++ l *** x) +++
     (iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR)
     +++  (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x) = idR).
apply fun_ext. move => r. smt.
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l +++ l *** x) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR +++
      (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x) = idR)
 = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR +++
      (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x)  = idR).
     apply fun_ext. move => r.
smt.
have ->: (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j +++ - (2 ^ w - 1) *** x)) idR +++
      (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x)  = idR)
  = (fun (x : R) =>
     2 ^ w *** (multiScalarMul_Simpl s{hr} P{hr} i l) +++ (2 ^ w *** (l *** x)) +++
     iteri i0
       (fun (j : int) (acc : R) =>
          acc +++ (s{hr} j i *** P{hr} j)) idR +++ i0 *** - (2 ^ w - 1) *** x +++
     (s{hr} i0 i *** P{hr} i0) +++  - (2 ^ w - 1) *** x  = idR).
     apply fun_ext. move => r.
       pose k := 2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++ 2 ^ w *** (l *** r).

 
     rewrite  (iteriZZZZ (fun j => s{hr} j i *** P{hr} j) i0 _ (- (2 ^ w - 1) *** r)) . smt(). timeout 10. smt.
 

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++ 2 ^ w *** (l *** x) +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     i0 *** - (2 ^ w - 1) *** x +++ s{hr} i0 i *** P{hr} i0 +++
     - (2 ^ w - 1) *** x = idR)
   = (fun (x : R) =>
     (2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l  +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR     +++  s{hr} i0 i *** P{hr} i0) +++

     (- (2 ^ w - 1) *** x +++
     i0 *** - (2 ^ w - 1) *** x  +++
     2 ^ w *** (l *** x)) = idR).
apply fun_ext. move => r. timeout 10. smt.

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
      s{hr} i0 i *** P{hr} i0 +++
     (- (2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) =
     idR)
     =  (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     s{hr} i0 i *** P{hr} i0 +++ x = idR) \o (fun  x => (-(2 ^ w - 1) *** x +++ i0 *** - (2 ^ w - 1) *** x +++
      2 ^ w *** (l *** x)) ). smt().
     rewrite - dmapE. simplify.

have ->: (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
     s{hr} i0 i *** P{hr} i0 +++ x = idR)
     = (fun x => x = idR) \o (fun (x : R) =>
     2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
     iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j) idR +++
      s{hr} i0 i *** P{hr} i0 +++ x). smt().
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
  progress. rewrite invertmeP. auto.

progress. smt. 
   
have ->: (dmap r_distr
     (fun (x : R) =>
        2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j)
          idR +++
        s{hr} i0 i *** P{hr} i0 +++ x))
   = r_distr.
apply (dmap_bij r_distr r_distr _ (fun (x : R) =>   -  (2 ^ w *** multiScalarMul_Simpl s{hr} P{hr} i l +++
        iteri i0 (fun (j : int) (acc : R) => acc +++ s{hr} j i *** P{hr} j)
          idR +++
         s{hr} i0 i *** P{hr} i0)  +++ x )).
progress. apply r_distr_full.
progress. apply r_distr_funi.
progress. timeout 10. smt.
progress. timeout 10. smt.
auto.
qed.



lemma completeness_final_DONE argP args &m : 
  Pr[ MultiScalarMul(UniformU).run(argP,args) @&m : !res.`1 ]
       <= ((p2 argP args) + (T%r * (l%r * (p1 + p1)))).
rewrite compl_flags.
rewrite - compl_II_equiv.
byphoare (_: arg = (argP , args) ==> _).
apply completeness_I.   auto. auto.
qed.  
