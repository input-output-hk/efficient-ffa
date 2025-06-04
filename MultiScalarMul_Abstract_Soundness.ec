require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract MultiScalarMul_Abstract_Setup.
require import IterationProps.


section.

declare module O <: OutCalls.
declare axiom  O_lossless : islossless O.getU. 

lemma MSM_soundness_param_u_ph argP args  argU : 
 phoare [ MSM.multiScalarMulMain_Opt_Corrected : 
  arg = (argP, args, argU) 
     ==>  res.`1 => res.`2 = (multiScalarMul_Simpl args argP T l) ] = 1%r.
proof.
bypr.
progress.
have ih: 1%r = Pr[MSM.completeMain(P{m}, s{m}, U{m}) @ &m 
  : res.`2 = multiScalarMul_Simpl args argP T l].
byphoare (_: arg = (argP, args, argU) ==> _).
conseq (multiscalarR_spec_ph argP args argU). smt(). auto.
have : Pr[MSM.multiScalarMulMain_Opt_Corrected(P{m}, s{m}, U{m}) @ &m :
   res.`1 => res.`2 = multiScalarMul_Simpl args argP T l] >=
Pr[MSM.completeMain(P{m}, s{m}, U{m}) @ &m :
   res.`2 = multiScalarMul_Simpl args argP T l].
byequiv (_: ={glob O} /\ arg{2} = (P{m}, s{m}, U{m}) /\ arg{1} = (P{m}, s{m}, U{m}) ==> res{2}.`1 => res{2}.`2 = res.`2{1} ).
proc*.
ecall (complete_optimized_equiv argP args argU).
skip. progress. smt(). smt(). smt(). auto.
smt().
smt.
auto. 
smt.
smt.
qed.


lemma MSM_soundness argP args &m : 
 Pr[ MultiScalarMul(O).run(argP, args) @&m : 
    res.`1 => res.`2 = (multiScalarMul_Simpl args argP T l) ] = 1%r.
proof.
byphoare (_:   arg = (argP, args)  ==> _).
proc.
seq 1 : #pre.
call (_: true). auto.
call (_: true). auto.
apply O_lossless.
auto.   
exists* u_cand. elim*. move => u_candV.
call (MSM_soundness_param_u_ph argP args u_candV).
wp.   skip. progress. 
hoare. simplify. call(_:true). auto. auto. auto. auto.
qed.   


end section.
