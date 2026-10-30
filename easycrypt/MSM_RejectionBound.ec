require import AllCore Distr Int IntDiv StdOrder List Finite.
require import AuxResults MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
 MultiScalarMul_Abstract_Completeness MSM_TableConstruction MSM_WithTable.
import IntOrder.

(* Union bound for a finite integer interval; no independence is assumed. *)
lemma mu_exists_interval ['a] (d : 'a distr) (E : int -> 'a -> bool)
 (lo n : int) (eps : real) :
 0 <= n =>
 (forall i, lo <= i < lo+n => mu d (E i) <= eps) =>
 mu d (fun x => exists i, lo <= i < lo+n /\ E i x) <= n%r * eps.
proof.
elim/natind: n.
+ move=> n Hn Hnonneg Hbound.
  have ->: n = 0 by smt().
  have ->: (fun x => exists i, lo <= i < lo+0 /\ E i x) = (fun x => false)
    by apply fun_ext; smt().
  rewrite mu0. smt().
+ move=> n Hn IH Hnonneg Hbound.
  have ->: (fun x => exists i, lo <= i < lo+(n+1) /\ E i x) =
    (fun x => (exists i, lo <= i < lo+n /\ E i x) \/ E (lo+n) x)
    by apply fun_ext; smt().
  have Hprev: mu d (fun x => exists i, lo <= i < lo+n /\ E i x) <= n%r * eps
    by apply IH; smt().
  have Hlast: mu d (E (lo+n)) <= eps by apply Hbound; smt().
  have Hunion := mu_or_leq_param d (n%r*eps) eps _ _ Hprev Hlast.
  smt().
qed.

(* Multiplication by n must be invertible on this group. *)
op scalar_invertible (n : int) =
 forall x, invertme n *** (n *** x) = x.

lemma scalar_invertible_small n : 0 < `|n| < order => scalar_invertible n.
proof. rewrite /scalar_invertible. smt(invertmeP). qed.

lemma scalar_event_mass n y : scalar_invertible n =>
 mu r_distr (fun u => n *** u = y) = p1.
proof.
move=> Hinv.
have Hmap: dmap r_distr (fun u => n *** u) = r_distr.
 apply (dmap_bij r_distr r_distr (fun u => n *** u) (fun u => invertme n *** u)).
 + progress. apply r_distr_full.
 + progress. apply r_distr_funi.
 + rewrite /scalar_invertible in Hinv. smt().
 + rewrite /scalar_invertible in Hinv. smt(nmul_mul).
have ->: (fun u => n *** u = y) = (fun x => x = y) \o (fun u => n *** u) by smt().
rewrite -dmapE Hmap /p1.
exact (r_distr_funi y idR).
qed.


lemma row_rejection_bound P b : 0 < b => P <> idR =>
 scalar_invertible (b-1) =>
 mu r_distr (fun u => ! row_safe P ((b-1) *** u) b) <= (b+1)%r * p1.
proof.
move=> Hb HP Hinv.
apply (RealOrder.ler_trans
 (mu r_distr (fun u => exists k, -1 <= k < -1+(b+1) /\ (b-1) *** u = k *** P))).
+ apply mu_sub. move=> u Hbad.
  have H := row_admissible_safe P ((b-1) *** u) b Hb.
  rewrite /row_admissible in H. smt().
apply (mu_exists_interval r_distr (fun k u => (b-1) *** u = k *** P) (-1) (b+1) p1).
+ smt().
+ move=> k Hk. rewrite (scalar_event_mass (b-1) (k *** P) Hinv). smt().
qed.

op nonzero_bases (P : int -> R) = forall j, 0 <= j < l => P j <> idR.

lemma table_rejection_bound P : nonzero_bases P =>
 scalar_invertible (2 ^ w - 1) =>
 mu r_distr (fun u => ! table_safe P u) <= l%r * ((2 ^ w + 1)%r * p1).
proof.
move=> HP Hinv.
apply (RealOrder.ler_trans
 (mu r_distr (fun u => exists j, 0 <= j < 0+l /\
  ! row_safe (P j) ((2 ^ w - 1) *** u) (2 ^ w)))).
+ apply mu_sub. rewrite /table_safe. smt().
apply (mu_exists_interval r_distr
 (fun j u => ! row_safe (P j) ((2 ^ w - 1) *** u) (2 ^ w)) 0 l ((2 ^ w + 1)%r * p1)).
+ smt(param_pos).
+ move=> j Hj. apply row_rejection_bound.
  + smt(expr_gt0).
  + move: HP. rewrite /nonzero_bases. smt().
  + exact Hinv.
qed.

op loop_ok P s u =
 (multiScalarMulLoop T l (perfect_table_pure P u) s (l *** u) w).`1.

op construction_accepts P s u =
 table_safe P u /\ valid_windows s /\ l *** u <> idR /\ loop_ok P s u.

op rejection_bound : real = (1 + l * (2 ^ w + 1) + 2*T*l)%r * p1.

lemma construction_failure_mass P s :
 nonzero_bases P => valid_windows s =>
 scalar_invertible (2 ^ w - 1) => scalar_invertible l =>
 mu r_distr (fun u => ! construction_accepts P s u) <= rejection_bound.
proof.
move=> HP Hs Htable Hinitial.
have Hrow := table_rejection_bound P HP Htable.
have Hinit := scalar_event_mass l idR Hinitial.
have Hloop := MSM_loop_failure_bound P s.
have ->: (fun u => ! construction_accepts P s u) =
 (fun u => ! table_safe P u \/ (l *** u = idR \/ !loop_ok P s u))
 by apply fun_ext; rewrite /construction_accepts; smt().
apply (RealOrder.ler_trans
 (l%r * ((2 ^ w + 1)%r * p1) + (p1 + T%r * (l%r * (p1 + p1))))).
+ apply mu_or_leq_param.
  + exact Hrow.
  + apply mu_or_leq_param.
    + smt().
    + exact Hloop.
rewrite /rejection_bound. smt(Real.fromintD Real.fromintM).
qed.


lemma complete_flag_spec argP args argU :
 phoare [MSM.completeMain : arg = (argP,args,argU) ==>
  res.`1 = (u_check argU argP args /\ loop_ok argP args argU)] = 1%r.
proof.
proc.
ecall (completeMainLoop_spec_ph2 argP args argU T _).
+ wp. skip. rewrite /loop_ok. progress; smt().
+ smt(param_pos).
qed.

lemma optimized_flag_spec argP args argU :
 phoare [MSM.multiScalarMulMain_Opt_Corrected : arg = (argP,args,argU) ==>
  res.`1 = (u_check argU argP args /\ loop_ok argP args argU)] = 1%r.
proof.
bypr. move=> &m Harg.
have ->: Pr[MSM.multiScalarMulMain_Opt_Corrected(P{m},s{m},U{m}) @ &m :
 res.`1 = (u_check argU argP args /\ loop_ok argP args argU)] =
 Pr[MSM.completeMain(argP,args,argU) @ &m :
 res.`1 = (u_check argU argP args /\ loop_ok argP args argU)].
+ byequiv (_: arg{1} = (argP,args,argU) /\ ={P,s,U} ==> res{1}.`1 = res{2}.`1).
  + symmetry. conseq (complete_optimized_equiv argP args argU); smt().
  + smt().
  + smt().
byphoare (complete_flag_spec argP args argU); smt().
qed.

lemma supplied_table_flag_spec argP args argU argTable :
 phoare [ConstructedMSM.with_table :
  arg = (argP,args,argU,argTable) /\ valid_windows args /\
  table_matches argTable argP argU /\ table_safe argP argU ==>
  res.`1 = construction_accepts argP args argU] = 1%r.
proof.
bypr. move=> &m Harg.
have ->: Pr[ConstructedMSM.with_table(P{m},s{m},U{m},table{m}) @ &m :
 res.`1 = construction_accepts argP args argU] =
 Pr[MSM.multiScalarMulMain_Opt_Corrected(argP,args,argU) @ &m :
 res.`1 = (u_check argU argP args /\ loop_ok argP args argU)].
+ byequiv with_table_equiv; rewrite /construction_accepts; smt(table_safe_u_check u_check_initial).
byphoare (optimized_flag_spec argP args argU); smt().
qed.

lemma constructed_flag_spec argP args argU :
 phoare [ConstructedMSM.run : arg = (argP,args,argU) ==>
  res.`1 = construction_accepts argP args argU] = 1%r.
proof.
proc.
seq 1 : (P = argP /\ s = args /\ U = argU /\
 built = table_safe argP argU /\ (built => table_matches table argP argU)).
+ call (table_build_spec_h argP argU). auto.
+ call (table_build_spec argP argU).
  skip. rewrite /table_matches. progress; smt().
+ sp 1. if.
  + ecall (supplied_table_flag_spec argP args argU table); skip; progress; smt().
  + wp. skip. rewrite /construction_accepts. progress; smt().
+ hoare. call (table_build_spec_h argP argU).
  skip. rewrite /table_matches. progress; smt().
+ auto.
qed.


(* Proof-only functional view of the acceptance event. *)
module ConstructionEvent = {
 proc run(P : int -> R, s : int -> int -> int) = {
  var u : R;
  u <$ r_distr;
  return construction_accepts P s u;
 }
}.

lemma construction_event_equiv :
 equiv [SampledConstructedMSM.run ~ ConstructionEvent.run :
  ={P,s} ==> res{1}.`1 = res{2}].
proof.
proc.
ecall {1} (constructed_flag_spec P{1} s{1} u{1}).
rnd. skip. progress; smt().
qed.

lemma sampled_rejection_mass argP args &m :
 Pr[SampledConstructedMSM.run(argP,args) @ &m : !res.`1] =
 mu r_distr (fun u => !construction_accepts argP args u).
proof.
have ->: Pr[SampledConstructedMSM.run(argP,args) @ &m : !res.`1] =
 Pr[ConstructionEvent.run(argP,args) @ &m : !res].
+ byequiv construction_event_equiv; smt().
byphoare (_: arg = (argP,args) ==> _).
+ proc. rnd. skip. progress.
+ auto.
+ auto.
qed.

lemma sampled_rejection_bound P s &m :
 nonzero_bases P => valid_windows s =>
 scalar_invertible (2 ^ w - 1) => scalar_invertible l =>
 Pr[SampledConstructedMSM.run(P,s) @ &m : !res.`1] <= rejection_bound.
proof.
move=> HP Hs Htable Hinitial.
rewrite sampled_rejection_mass.
exact (construction_failure_mass P s HP Hs Htable Hinitial).
qed.


(* Full support and uniformity make this a finite enumeration of R. *)
op group_elements : R list = to_seq (support r_distr).
op group_cardinality : int = size group_elements.

lemma group_elements_complete x : x \in group_elements.
proof.
rewrite /group_elements mem_to_seq.
+ exact (uniform_finite r_distr r_distr_uni).
+ exact (r_distr_full x).
qed.

lemma group_elements_unique : uniq group_elements.
proof. rewrite /group_elements. exact uniq_to_seq. qed.

lemma group_cardinality_positive : 0 < group_cardinality.
proof.
have H := group_elements_complete idR.
rewrite /group_cardinality. smt(size_ge0 size_eq0 in_nil).
qed.

lemma point_mass_cardinality : p1 = 1%r / group_cardinality%r.
proof.
rewrite /p1 /group_cardinality /group_elements.
have ->: (fun (x : R) => x = idR) = pred1 idR
 by apply fun_ext; rewrite /pred1; smt().
by rewrite (mu1_uni_ll r_distr idR r_distr_uni r_distr_ll) (r_distr_full idR) /=.
qed.

lemma sampled_rejection_bound_cardinality P s &m :
 nonzero_bases P => valid_windows s =>
 scalar_invertible (2 ^ w - 1) => scalar_invertible l =>
 Pr[SampledConstructedMSM.run(P,s) @ &m : !res.`1]
 <= (1 + l * (2 ^ w + 1) + 2*T*l)%r / group_cardinality%r.
proof.
move=> HP Hs Htable Hinitial.
have H := sampled_rejection_bound P s &m HP Hs Htable Hinitial.
move: H. rewrite /rejection_bound point_mass_cardinality. smt().
qed.


lemma sampled_constructed_lossless : islossless SampledConstructedMSM.run.
proof.
proc*. ecall (sampled_constructed_msm_soundness P s); auto.
qed.

lemma sampled_success_bound_cardinality P s &m :
 nonzero_bases P => valid_windows s =>
 scalar_invertible (2 ^ w - 1) => scalar_invertible l =>
 1%r - (1 + l * (2 ^ w + 1) + 2*T*l)%r / group_cardinality%r
 <= Pr[SampledConstructedMSM.run(P,s) @ &m : res.`1].
proof.
move=> HP Hs Htable Hinitial.
have Hfail := sampled_rejection_bound_cardinality P s &m HP Hs Htable Hinitial.
have Htotal: Pr[SampledConstructedMSM.run(P,s) @ &m : true] = 1%r
 by byphoare sampled_constructed_lossless.
move: Hfail. rewrite Pr [mu_not] Htotal. smt().
qed.

(* Sufficient numerical conditions using the existing scalar-inversion axiom. *)
lemma sampled_rejection_bound_small_scalars P s &m :
 nonzero_bases P => valid_windows s =>
 0 < `|(2 ^ w - 1)| < order => 0 < `| l| < order =>
 Pr[SampledConstructedMSM.run(P,s) @ &m : !res.`1]
 <= (1 + l * (2 ^ w + 1) + 2*T*l)%r / group_cardinality%r.
proof.
move=> HP Hs Htable Hinitial.
apply (sampled_rejection_bound_cardinality P s &m HP Hs);
 apply scalar_invertible_small; assumption.
qed.
