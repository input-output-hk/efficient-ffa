require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract MultiScalarMul_Abstract_Setup.
require import IterationProps.

section.

declare module O <: OutCalls.
 
declare axiom tablePT_ph parg varg : phoare [ O.getPT : arg = (parg,varg)
   ==> res.`1 => (res.`2 = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  /\ (forall i j, res.`2 i j <> idR) )   ] = 1%r.


lemma tablePT parg varg : hoare [ O.getPT : arg = (parg,varg)
   ==> res.`1 => (res.`2 = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  /\ (forall i j, res.`2 i j <> idR) )   ].
proof. conseq (tablePT_ph parg varg). auto. qed.
   

(* lemma helpereqs argacc argtable argic args  :  *)
(*  equiv [ SimpleComp.completeAddLoop ~ SimpleComp.incompleteAddLoop :  *)
(*   arg{2} = (argacc, argtable, argic, args) /\ ={acc,table,ic,s} *)
(*        /\ (forall i j, table{1} i j <> idR) *)
(*      ==>  res{2}.`1 => (res{1} = res{2}.`2)]. *)
(* proc. *)
(* while (={jc,acc,table,aux,s,ic} /\ (flag{2} => ={vahe}) *)
(*  /\ (forall i j, table{1} i j <> idR)). *)
(*  wp. skip. progress. *)
(*    have -> : vahe{1} = vahe{2}. smt(). *)
(* rewrite same_res.  admit. *)
(*   smt(). *)
(*   smt().  *)
(*   smt(). *)
(*   (* smt(). *) *)
(* wp. skip. progress.  *)
(* qed. *)


lemma multieqs argP args argU  :
 equiv [ SimpleComp.multiScalarMulR 
        ~ MultiScalarMul(O).multiScalarMulI :
  arg{2} = (argP, args, argU) /\ ={P,s,U} /\ ={glob O}
     ==>  res{2}.`1 => (res{1} = res{2}.`2)].
proc.
wp.
while ((flag{2} => ={table,acc,U,s} /\ (forall i j, table{2} i j <> idR)) /\ (flag{2} => flagaux{2}) /\ ={ic}  ).
wp.
inline SimpleComp.completeAddLoop.
inline SimpleComp.incompleteAddLoop.   
wp.
while ((flag{2} /\ flag0{2} => ={vahe, acc0,table0,aux0,s0,ic0} /\ (forall i j, table0{2} i j <> idR) /\ vahe{2} <> idR) /\ ={jc0} ).
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
apply opt_never_id. smt(). smt().
smt().
wp.
ecall {1} (doublewtimes_spec_ph acc{1} w).
ecall {2} (doublewtimes_spec_ph acc{2} w).
skip. progress. 
smt(w_pos). smt(). smt(). smt().
smt(). smt().
apply no_order_two_elems. smt(w_pos).
smt(). smt(). smt().
smt(). smt().    
wp. 
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
have ih: 1%r = Pr[SimpleComp.multiScalarMulR(P{m}, s{m}, U{m}) @ &m 
  : res = multiScalarMulR args argP].
byphoare (_: arg = (argP, args, argU) ==> _).
conseq (multiscalarR_spec_ph argP args argU). smt(). auto.
have : Pr[MultiScalarMul(O).multiScalarMulI(P{m}, s{m}, U{m}) @ &m :
   res.`1 => res.`2 = multiScalarMulR args argP] >=
Pr[SimpleComp.multiScalarMulR(P{m}, s{m}, U{m}) @ &m :
   res = multiScalarMulR args argP].
byequiv (_: ={glob O} /\ arg{2} = (P{m}, s{m}, U{m}) /\ arg{1} = (P{m}, s{m}, U{m}) ==> res{2}.`1 => res{2}.`2 = res{1} ).
proc*.
ecall (multieqs argP args argU).
skip. progress. smt(). smt(). smt(). 
auto.
smt().
smt.
auto.
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
