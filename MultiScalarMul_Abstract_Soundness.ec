require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract MultiScalarMul_Abstract_Setup.
require import IterationProps.

section.

declare module O <: OutCalls.

declare axiom O_lossless : islossless O.getU. 

lemma multieqs2 argP args argU  :
 equiv [ SimpleComp.multiScalarMulMain_Perfect 
        ~ SimpleComp.multiScalarMulMain_Opt_Corrected :
  arg{2} = (argP, args, argU) /\ ={P,s,U} /\ ={glob O}
     ==>  res{2}.`1 => (res{1} = res{2}.`2)].
proc.
wp.
inline SimpleComp.multiScalarMulMain_Opt. wp.
while ((flag0{2} => ={table,acc,U,s} /\ (forall i j, table{2} i j <> idR)) /\ (flag0{2} => flagaux{2}) /\ ={ic} /\ s{1} = s0{2}  ).
wp.
inline SimpleComp.completeAddLoop.
inline SimpleComp.incompleteAddLoop.   
wp.
while ((flag0{2} /\ flag1{2} => ={vahe, acc0,table0,aux0,s0,ic0} /\ (forall i j, table0{2} i j <> idR) /\ vahe{2} <> idR) /\ ={jc0} /\ s0{1} = s1{2} ).
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
smt(). 
apply no_order_two_elems. smt(w_pos).
smt(). smt(). smt().
smt(). smt().    
wp. 
 skip. progress. admit. smt().
qed.




lemma multiscalarI_spec_ph argP args  argU : 
 phoare [ SimpleComp.multiScalarMulMain_Opt_Corrected : 
  arg = (argP, args, argU) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] = 1%r.
proof.
bypr.
progress.
have ih: 1%r = Pr[SimpleComp.multiScalarMulMain_Perfect(P{m}, s{m}, U{m}) @ &m 
  : res = multiScalarMulR args argP].
byphoare (_: arg = (argP, args, argU) ==> _).
conseq (multiscalarR_spec_ph argP args argU). smt(). auto.
have : Pr[SimpleComp.multiScalarMulMain_Opt_Corrected(P{m}, s{m}, U{m}) @ &m :
   res.`1 => res.`2 = multiScalarMulR args argP] >=
Pr[SimpleComp.multiScalarMulMain_Perfect(P{m}, s{m}, U{m}) @ &m :
   res = multiScalarMulR args argP].
byequiv (_: ={glob O} /\ arg{2} = (P{m}, s{m}, U{m}) /\ arg{1} = (P{m}, s{m}, U{m}) ==> res{2}.`1 => res{2}.`2 = res{1} ).
proc*.
ecall (multieqs2 argP args argU).
skip. progress. smt(). smt(). smt(). 
auto.
smt().
smt.
auto.
smt.
qed.


lemma multiscalar_spec_h argP args : 
 phoare [ MultiScalarMul(O).run : 
  arg = (argP, args) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] = 1%r .
proc.
seq 1 : #pre.
call (_: true). auto.
call (_: true). auto.
apply O_lossless.
 auto.   

exists* u_cand. elim*. move => u_candV.
call (multiscalarI_spec_ph  argP args u_candV).
wp.   skip. progress.
hoare. simplify. call(_:true). auto. auto.
 qed.   


end section.
