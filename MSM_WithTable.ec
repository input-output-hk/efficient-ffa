require import AllCore Int StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
 MultiScalarMul_Abstract_Soundness MultiScalarMul_Abstract_Completeness MSM_TableConstruction.

op table_matches (table : int -> int -> R) P U =
 forall j k, 0 <= j < l => 0 <= k < 2 ^ w =>
  table j k = perfect_table_pure P U j k.

module ConstructedMSM = {
 proc with_table(P : int -> R, s : int -> int -> int, U : R,
                 table : int -> int -> R) = {
  var acc : R;
  var ic : int;
  var accepted, flag, step_ok : bool;
  accepted <- l *** U <> idR;
  flag <- true;
  acc <- l *** U;
  ic <- 0;
  while (ic < T) {
   acc <@ MSM.doubleLoop(acc,w);
   (step_ok, acc) <@ MSM.incompleteAddLoop(acc,table,ic,s);
   flag <- flag /\ step_ok;
   ic <- ic + 1;
  }
  return (accepted /\ flag, acc +++ -(l *** U));
 }

 proc run(P : int -> R, s : int -> int -> int, U : R) = {
  var table : int -> int -> R;
  var built : bool;
  var result : bool * R;
  (built, table) <@ TableBuilder.build(P,U);
  result <- (false,idR);
  if (built /\ valid_windows s) {
   result <@ with_table(P,s,U,table);
  }
  return result;
 }
}.


lemma add_loop_table_equiv :
 equiv [MSM.incompleteAddLoop ~ MSM.incompleteAddLoop :
  ={acc,ic,s} /\
  (forall j, 0 <= j < l => table{1} j (s{1} j ic{1}) = table{2} j (s{2} j ic{2}))
  ==> ={res}].
proof.
proc.
while (={acc,ic,s,jc,vahe,flag} /\ 0 <= jc{1} <= l /\
  (forall j, 0 <= j < l => table{1} j (s{1} j ic{1}) = table{2} j (s{2} j ic{2}))).
+ wp. skip. progress; smt().
wp. skip. progress; smt(param_pos).
qed.

lemma with_table_equiv :
 equiv [ConstructedMSM.with_table ~ MSM.multiScalarMulMain_Opt_Corrected :
  ={P,s,U} /\ valid_windows s{1} /\ table_matches table{1} P{1} U{1} /\ table_safe P{1} U{1}
  ==> ={res}].
proof.
proc.
inline MSM.multiScalarMulMain_Opt.
wp.
while (={P,s,U,acc,ic} /\ s0{2} = s{1} /\
 flag{1} = flag0{2} /\ accepted{1} = flag{2} /\ 0 <= ic{1} <= T /\
 table{2} = perfect_table_pure P{2} U{2} /\
 table_matches table{1} P{1} U{1} /\ valid_windows s{1} /\ table_safe P{1} U{1}).
+ wp.
  call add_loop_table_equiv.
  call (_: true). sim.
  skip. rewrite /table_matches /valid_windows. progress; smt().
wp. skip. progress; smt(param_pos table_safe_u_check u_check_initial).
qed.


lemma with_table_soundness argP args argU argTable :
 phoare [ConstructedMSM.with_table :
  arg = (argP,args,argU,argTable) /\
  valid_windows args /\ table_matches argTable argP argU /\ table_safe argP argU ==>
  res.`1 => res.`2 = multiScalarMul_Simpl args argP T l] = 1%r.
proof.
bypr. move=> &m Harg.
have ->: Pr[ConstructedMSM.with_table(P{m},s{m},U{m},table{m}) @ &m :
 res.`1 => res.`2 = multiScalarMul_Simpl args argP T l] =
 Pr[MSM.multiScalarMulMain_Opt_Corrected(argP,args,argU) @ &m :
 res.`1 => res.`2 = multiScalarMul_Simpl args argP T l].
+ byequiv with_table_equiv; smt().
byphoare (MSM_soundness_param_u_ph UniformU UniformU_lossless argP args argU); smt().
qed.

lemma constructed_msm_soundness argP args argU :
 phoare [ConstructedMSM.run : arg = (argP,args,argU) ==>
  res.`1 => res.`2 = multiScalarMul_Simpl args argP T l] = 1%r.
proof.
proc.
seq 1 : (P = argP /\ s = args /\ U = argU /\
 built = table_safe argP argU /\ (built => table_matches table argP argU)).
+ call (table_build_spec_h argP argU). auto.
+ call (table_build_spec argP argU).
  skip. rewrite /table_matches. progress; smt().
+ sp 1. if.
  + ecall (with_table_soundness argP args argU table); skip; progress; smt().
  + wp. skip. progress; smt().
+ hoare. call (table_build_spec_h argP argU).
  skip. rewrite /table_matches. progress; smt().
+ auto.
qed.


module SampledConstructedMSM = {
 proc run(P : int -> R, s : int -> int -> int) = {
  var u : R;
  var result : bool * R;
  u <$ r_distr;
  result <@ ConstructedMSM.run(P,s,u);
  return result;
 }
}.

lemma sampled_constructed_msm_soundness argP args :
 phoare [SampledConstructedMSM.run : arg = (argP,args) ==>
  res.`1 => res.`2 = multiScalarMul_Simpl args argP T l] = 1%r.
proof.
proc.
ecall (constructed_msm_soundness argP args u).
rnd. skip. progress; smt(r_distr_ll).
progress; smt(r_distr_ll).
qed.
