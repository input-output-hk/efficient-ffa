require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.


require import MultiScalarMul_Abstract MultiScalarMul_Abstract_Setup AuxResults IterationProps.
require import Distr.

(* add group order premise n < p *)
axiom funny_one n b :  exists (x : R), n *** x = b.

(* only if gcd(n,order) = 1 *)
axiom const_mul_inj : forall n, 1 <= n => forall x y, n *** x = n *** y => x = y.

op p1 : real.
axiom p1_prop x : mu r_distr (fun r => x = xof r) <= p1.

op p2 P s : real = mu r_distr (fun (x : R) => ! u_check x P s).



lemma incompleteAddLoop_specR_ph argcc argT argic args  :
 phoare [ SimpleComp.incompleteAddLoop : arg = (argcc, argT, argic,  args)
     ==>  res = helperI_pure l argT args argic argcc ] = 1%r.
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
     ==>  res = helperI_pure l argT args argic argcc ].
conseq (incompleteAddLoop_specR_ph argcc argT argic args).
qed.   


lemma multm_spec_h argP args argU  :
 hoare [ SimpleComp.multiScalarMulMain_Opt : arg = (argP, args, argU)   
  ==>  res = multiScalarMulII_pure T l (perfect_table_pure argP argU) args (l *** argU) w   ] .
proc. 
while (
  0 <= ic 
  /\ ic <= T
  /\ (U, table, s) = (argU, (perfect_table_pure argP argU), args) 
  /\ (flag , acc) = multiScalarMulII_pure ic l ((perfect_table_pure argP argU)) args (l *** argU) w
 ) .
wp.
ecall (incompleteAddLoop_specR_h acc (perfect_table_pure argP argU) ic args).
ecall (doublewtimes_spec acc w). 
skip.
progress. smt(w_pos).
smt(). smt().
rewrite /multiScalarMulII_pure.
rewrite iteriS. smt().
smt().
wp. skip. progress. smt(T_pos).   
rewrite /multiScalarMulII_pure. rewrite iteri0.
auto. auto. 
have -> : T = ic0. smt(T_pos).
rewrite - H2.
 smt().
qed. 


lemma multm_spec_ph argP args argU  :
 phoare [ SimpleComp.multiScalarMulMain_Opt : arg = (argP, args, argU)   
  ==>  res = multiScalarMulII_pure T l (perfect_table_pure argP argU) args (l *** argU) w ]  = 1%r.
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



lemma completeness_I argP args :
  phoare [ SimpleComp.multiScalarMul_Fun :
      arg = (argP , args) ==> !res.`1 ] 
            <= ((p2 argP args) + (T%r * (l%r * p1))).
proc.
wp. rnd. skip. progress. 
rewrite /multiScalarMulII_pure.
pose f := fun a i b => 
  (helperI_pure l (perfect_table_pure P{hr} a)
    s{hr} i (2 ^ w *** b)).
simplify.
rewrite mu_split. simplify.
apply mu_split_q.
apply kkkk. smt().
auto.
apply (iteri_ub (fun (x : R) => l *** x) f  r_distr (l%r * p1) _ T _)  .  
move => i acc.
rewrite /f. rewrite /helperI_pure.   
pose h := fun  a j b
    =>  ((xdiff b
               (perfect_table_pure P{hr} ( a) j (s{hr} j i)))
        , b %%% perfect_table_pure P{hr} ( a) j (s{hr} j i)).
apply  (iteri_ub (fun (x : R) => 2 ^ w *** acc) h r_distr p1).  
progress.
rewrite /h. simplify.           
rewrite /perfect_table_pure. simplify.
rewrite /xdiff.            
simplify.
 have -> : (fun (r : R) =>
     xof (acc0) = xof (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** r))
     = (fun (r : F) =>
     xof (acc0 ) = r) \o (fun r =>  xof (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** r)) . smt().
rewrite - dmapE. simplify.
rewrite - dmap_comp.
 have  ->:  ((dmap r_distr
        (fun (x : R) => s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x)))
   = r_distr.
    have -> : dmap r_distr (fun (x : R) => s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x) =
       dmap r_distr ((fun (x : R) => s{hr} i0 i *** P{hr} i0 +++ x) \o (fun x => - (2 ^ w - 1) *** x)). smt ().
rewrite - dmap_comp.
   have -> : (fun (x0 : R) => - (2 ^ w - 1) *** x0)
    = (fun (x0 : R) => - x0) \o (fun x => (2 ^ w - 1) *** x).   smt().
     rewrite - dmap_comp.
    have ->: (dmap r_distr (fun (x0 : R) => (2 ^ w - 1) *** x0))  = r_distr.
    pose  funny_op := fun (a : R) => choiceb (fun (x : R) => (2 ^ w - 1) *** x = a) witness.
      apply (dmap_bij _ _ _ funny_op).
     progress. apply r_distr_full.
     progress. apply r_distr_funi.
    progress.
    rewrite /funny_op.
    pose xxx := choiceb (fun (x : R) => (2 ^ w - 1) *** x = (2 ^ w - 1) *** a) witness.
      have : (2 ^ w - 1) *** xxx = (2 ^ w - 1) *** a.
     
    apply (choicebP (fun (x : R) => (2 ^ w - 1) *** x = (2 ^ w - 1) *** a)). exists a. auto. 
    
    progress.
    apply (const_mul_inj (2 ^ w - 1)). smt. auto.
    rewrite /funny_op.
    progress.
    apply (choicebP (fun (x : R) => (2 ^ w - 1) *** x = b)).
    simplify.
    apply (funny_one (2 ^ w - 1) b).
    have ->: (dmap r_distr (fun (x0 : R) => -x0)) = r_distr.
    apply (dmap_bij _ _ _ ((fun (x : R) => - x ))).    
    progress. apply r_distr_full.
    progress. apply r_distr_funi.
    progress. apply neg_neg_id.
    progress. apply neg_neg_id.
    apply (dmap_bij _ _ _ ((fun (x : R) => x +++ - s{hr} i0 i *** P{hr} i0 ))).
    progress. apply r_distr_full.
    progress. apply r_distr_funi.
    progress. smt (op_assoc op_comm op_id op_id' op_inv).
    progress. smt (op_assoc op_comm op_id op_id' op_inv).
rewrite  dmapE.    
apply p1_prop.
    smt(l_pos).
    smt(T_pos).
qed.           

(*
TODO:

1/ define multiScalarMul with perfect +++ but still doing the flag check
2/ prove that !flag is same in both cases
3/ analyze the !flag case

  *)
