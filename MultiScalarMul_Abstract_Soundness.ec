require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract.
require import IterationProps.

section.

declare module O <: OutCalls.
declare module O_Partial <: OutCalls.

declare axiom tableP parg varg : hoare [ O.getT : arg = (parg,varg)
   ==> res = (fun (j i : int) => (i *** (parg j)) +++ - varg)  ].

declare axiom tablePT parg varg : hoare [ O.getPT : arg = (parg,varg)
   ==> res.`1 => (res.`2 = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  /\ (forall i j, res.`2 i j <> idR) )   ].
 
declare axiom getT_lossless : islossless O.getT.

declare axiom tableP_ph parg varg : phoare [ O.getT : arg = (parg,varg)
   ==> res = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  ] = 1%r.

declare axiom tablePT_ph parg varg : phoare [ O.getPT : arg = (parg,varg)
   ==> res.`1 => (res.`2 = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  /\ (forall i j, res.`2 i j <> idR) )   ] = 1%r.

   

lemma helpereqs argacc argtable argic args  : 
 equiv [ SimpleComp.completeAddLoop ~ MultiScalarMul(O).helperI : 
  arg{2} = (argacc, argtable, argic, args) /\ ={acc,table,ic,s}
       /\ (forall i j, table{1} i j <> idR)
     ==>  res{2}.`1 => (res{1} = res{2}.`2)].
proc.
while (={jc,acc,table,aux,s,ic} /\ (flag{2} => ={vahe})
 /\ (forall i j, table{1} i j <> idR)).
 wp. skip. progress.
   have -> : vahe{1} = vahe{2}. smt().
rewrite same_res. 
  smt().
  smt(). 
  smt().
  smt().
wp. skip. progress. 
qed.

lemma multiscalarR_spec argP args argU : 
 hoare [ MultiScalarMul(O).multiScalarMulR : 
  arg = (argP, args, argU) 
     ==>  res = (multiScalarMulR  args argP)  ].
proc. wp.
while (0 <= ic
 /\ (2 ^ w - 1) *** U = v
 /\ table = (fun (j i : int) =>  (i *** (P j)) +++ - v)
 /\ ic <= T
 /\ acc = ((iteri ic
            (fun i acc1 => acc1 +++
              (iteri l
                 (fun j acc2 => acc2 +++ (2 ^ (w * (ic - 1 - i)) * s j i) *** (P j)) idR)
                 ) idR)) +++ l *** U).
wp.
ecall (helper_specR acc table ic s). simplify.
wp.
ecall (doublewtimes_spec acc w). skip. progress. smt(w_pos).
smt(). smt().
   rewrite mul_plus_distr.
rewrite iteriZ.           smt().
simplify.
have -> : iteri ic{hr}
  (fun (i : int) (acc0 : R) =>
     acc0 +++
     2 ^ w ***
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (ic{hr} - 1 - i)) * s{hr} j i *** P{hr} j) idR)
  idR
     = iteri ic{hr}
  (fun (i : int) (acc0 : R) =>
     acc0 +++
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (ic{hr}  - i )) * s{hr} j i *** P{hr} j) idR)
  idR.
apply eq_iteri.
progress.
rewrite iteriZ. smt(l_pos). congr.
     apply eq_iteri. move => j acc.
     progress. congr.
      have ->: 2 ^ w *** (2 ^ (w * (ic{hr} - 1 - i)) * s{hr} j i *** P{hr} j)
                = 2 ^ w * 2 ^ (w * (ic{hr} - 1 - i)) * s{hr} j i *** P{hr} j .
  rewrite mulsc. smt. smt().
        rewrite - exprD_nneg. smt(w_pos). smt(w_pos). smt().
pose v := (2 ^ w - 1) *** U{hr}.
have -> : iteri l
  (fun (j : int) (acc0 : R) => acc0 +++ (s{hr} j ic{hr} *** P{hr} j +++ -v))
  idR = iteri l
  (fun (j : int) (acc0 : R) => acc0 +++ (s{hr} j ic{hr} *** P{hr} j)) idR +++
     iteri l (fun (j : int) (acc0 : R) => acc0 +++ -v) idR.
rewrite - iteriZZ. simplify.
smt(l_pos). apply eq_iteri.  progress. smt.
simplify.
rewrite  iteriZZZ.
simplify. smt(l_pos).
rewrite kik .
have ->: (2 ^ w *** (l *** U{hr}) +++ l *** -v) = l *** U{hr}.
    rewrite /v.
  rewrite  mulsc. smt.
  have -> : l *** - (2 ^ w - 1) *** U{hr}
    = (l * - (2 ^ w - 1)) *** U{hr}. rewrite  nmul_mul.  rewrite neg_mul. auto.
   rewrite - nplus_dist. congr. smt().
rewrite iteriS.
smt(). simplify.
have ->: 2 ^ 0 = 1. smt(@Int).
smt().
wp.
ecall (tableP P v). wp. skip. progress. smt(T_pos).
rewrite iteri0. auto. smt.
rewrite /multiScalarMulInt.
have -> : ic0 = T. smt().
simplify.
  have ->: iteri T
  (fun (i : int) (acc1 : R) =>
     acc1 +++
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (T - 1 - i)) * s{hr} j i *** P{hr} j) idR) idR +++
l *** U{hr} +++ - l *** U{hr}
       = iteri T
  (fun (i : int) (acc1 : R) =>
     acc1 +++
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (T - 1 - i)) * s{hr} j i *** P{hr} j) idR) idR +++
  (l *** U{hr} +++ - l *** U{hr} ).
smt(op_assoc).
rewrite op_inv.
  rewrite op_id.
  rewrite /multiScalarMulR.
auto.
qed.


lemma multiscalarR_spec_ph argP args argU : 
 phoare [ MultiScalarMul(O).multiScalarMulR : 
  arg = (argP, args, argU) 
     ==>  res = (multiScalarMulR  args argP)  ] = 1%r.
phoare split ! 1%r 0%r. auto.
   proc. wp.
while true (T - ic). progress.
wp.
exists* acc, table, ic, s.
elim*. move => accV tableV icV sV.
call helper_specR_total.   
call (_: arg = (accV, MultiScalarMul_Abstract.w) ==> true).
proc*. call (doublewtimes_spec_ph accV MultiScalarMul_Abstract.w).
skip. progress. smt(w_pos). skip.
progress.
smt().
wp. call (_:true). apply getT_lossless. 
wp. skip. progress. smt().
hoare. simplify.   
apply multiscalarR_spec.
qed.


lemma multieqs argP args argU  :
 equiv [ MultiScalarMul(O).multiScalarMulR 
        ~ MultiScalarMul(O).multiScalarMulI :
  arg{2} = (argP, args, argU) /\ ={P,s,U} /\ ={glob O}
     ==>  res{2}.`1 => (res{1} = res{2}.`2)].
proc.
wp.
while ((flag{2} => ={table,acc,U,s} /\ (forall i j, table{2} i j <> idR)) /\ (flag{2} => flagaux{2}) /\ ={ic}  ).
wp.
inline SimpleComp.completeAddLoop.
inline MultiScalarMul(O).helperI.
wp.
while ((flag{2} /\ flag0{2} => ={vahe, acc0,table0,aux0,s0,ic0} /\ (forall i j, table0{2} i j <> idR)) /\ ={jc0}).
 wp. skip. progress.
   have -> : vahe{1} = vahe{2}. smt().
rewrite same_res.
  smt().
  smt().
  smt().
  smt().
     smt().
     smt().
     smt().
     smt().
     smt().
     smt().
wp.
inline SimpleComp.doubleLoop.
wp.
   while ((flag{2} => ={p}) /\ ={w,cnt0}). wp. skip. progress.
   smt(). wp. skip. progress.
smt(). smt(). smt(). smt(). smt(). smt().
   smt(). smt().  smt(). smt(). smt().
wp. 
ecall {1} (tableP_ph P{1} v{1} ).
ecall {2} (tablePT_ph P{2} v{2}).    
wp. skip. progress. smt(). smt().
have -> :     acc_L = acc_R. smt(). auto.
qed.


lemma multiscalarI_spec_ph argP args  argU : 
 phoare [ MultiScalarMul(O).multiScalarMulI : 
  arg = (argP, args, argU) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] = 1%r.
proof.
bypr.
progress.
have ih: 1%r = Pr[MultiScalarMul(O).multiScalarMulR(P{m}, s{m}, U{m}) @ &m 
  : res = multiScalarMulR args argP].
byphoare (_: arg = (argP, args, argU) ==> _).
conseq (multiscalarR_spec_ph argP args argU). smt(). auto.
have : Pr[MultiScalarMul(O).multiScalarMulI(P{m}, s{m}, U{m}) @ &m :
   res.`1 => res.`2 = multiScalarMulR args argP] >=
Pr[MultiScalarMul(O).multiScalarMulR(P{m}, s{m}, U{m}) @ &m :
   res = multiScalarMulR args argP].
byequiv (_: _ ==> res{2}.`1 => res{2}.`2 = res{1} ).
proc*.
ecall (multieqs argP args argU).
skip. progress. smt(). smt(). smt(). smt().
auto.
smt().
smt.
qed.


lemma multiscalarI_spec_h argP args  argU : 
 hoare [ MultiScalarMul(O).multiScalarMulI : 
  arg = (argP, args, argU) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] .
conseq (multiscalarI_spec_ph argP args argU).
qed.   


lemma multiscalar_spec_h argP args : 
 hoare [ MultiScalarMul(O).multiScalarMul : 
  arg = (argP, args) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] .
proc.
seq 1 : #pre.
call (_: true). auto.
sp. if.
  ecall (multiscalarI_spec_h P s (embed u_cand)).
   skip. progress.
wp. skip.
smt().
qed.   


end section.
