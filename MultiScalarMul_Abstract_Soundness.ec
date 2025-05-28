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



lemma multiscalarI_spec_ph argP args  argU : 
 phoare [ SimpleComp.multiScalarMulMain_Opt_Corrected : 
  arg = (argP, args, argU) 
     ==>  res.`1 => res.`2 = (multiScalarMul_Simpl args argP T l)  ] = 1%r.
proof.
bypr.
progress.
have ih: 1%r = Pr[SimpleComp.multiScalarMulMain_Perfect(P{m}, s{m}, U{m}) @ &m 
  : res.`2 = multiScalarMul_Simpl args argP T l].
byphoare (_: arg = (argP, args, argU) ==> _).
conseq (multiscalarR_spec_ph argP args argU). smt(). auto.
have : Pr[SimpleComp.multiScalarMulMain_Opt_Corrected(P{m}, s{m}, U{m}) @ &m :
   res.`1 => res.`2 = multiScalarMul_Simpl args argP T l] >=
Pr[SimpleComp.multiScalarMulMain_Perfect(P{m}, s{m}, U{m}) @ &m :
   res.`2 = multiScalarMul_Simpl args argP T l].
byequiv (_: ={glob O} /\ arg{2} = (P{m}, s{m}, U{m}) /\ arg{1} = (P{m}, s{m}, U{m}) ==> res{2}.`1 => res{2}.`2 = res.`2{1} ).
proc*.
ecall (multieqs2 argP args argU).
skip. progress. smt(). smt(). smt(). 
auto.
smt().
smt.
auto. 
smt.
smt.
qed.


lemma multiscalar_spec_h argP args : 
 phoare [ MultiScalarMul(O).run : 
  arg = (argP, args) 
     ==>  res.`1 => res.`2 = (multiScalarMul_Simpl  args argP T l)  ] = 1%r .
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
