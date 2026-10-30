require import AllCore IntDiv StdOrder Distr SmallCurve.
require import AffineComplete.
import Ring.IntID IntOrder.
import Concrete.MultiScalarMul_Abstract_Setup Concrete.MultiScalarMul_Abstract
  Concrete.MultiScalarMul_Abstract_Completeness Concrete.MSM_TableConstruction
  Concrete.MSM_CompleteCoordinates Concrete.MSM_RejectionBound Concrete.MSM_WindowOrder
  Concrete.MSM_FullCoordinates.

lemma sampler_point_mass (u : F7.zmod) : mu1 F7.DZmodP.dunifin u = 1%r / 7%r.
proof. by rewrite F7.DZmodP.dunifin1E F7.DZmodP.cardE. qed.

lemma cardinality_seven : group_cardinality=7.
proof.
have H := point_mass_cardinality.
have HP := group_cardinality_positive.
have E : p1=1%r/7%r.
+ rewrite /p1. have -> : (fun (x : F7.zmod) => x=F7.zero)=pred1 F7.zero
    by apply fun_ext=> x; rewrite /pred1; smt().
  exact (sampler_point_mass F7.zero).
have HR : group_cardinality%r=7%r by smt().
smt(Real.eq_fromint).
qed.

lemma one_invertible : scalar_invertible 1.
proof. apply scalar_invertible_small. trivial. qed.

(* Every accepted raw output equals the mathematical little-endian MSM.
   The representation and group hypotheses have all been discharged. *)
lemma concrete_sound P s u r :
  little_endian_full_constraints 5 2 (fun j => group_point cx cy (P j)) s (group_point cx cy u) r =>
  r=group_point cx cy (msm_little_endian s P 1 1).
proof. exact (little_endian_full_sound cx cy 5 2 1 P s u r coordinates complete_model). qed.

lemma concrete_failure_bound P s : nonzero_bases P => valid_windows s =>
  mu F7.DZmodP.dunifin (fun u => !exists r,
    little_endian_full_constraints 5 2 (fun j => group_point cx cy (P j)) s (group_point cx cy u) r)
  <= 6%r/7%r.
proof.
move=> HP Hs.
have H := little_endian_full_failure_bound cx cy 5 2 1 P s coordinates complete_model HP Hs _ one_invertible.
+ rewrite expr1 /=. exact one_invertible.
move: H. by rewrite cardinality_seven expr1 /=.
qed.

lemma concrete_program_rejection P s &mem :
  Pr[SampledLittleEndianMSM.run(P,s) @ &mem : !res.`1] =
  mu F7.DZmodP.dunifin (fun u => !exists r,
    little_endian_full_constraints 5 2 (fun j => group_point cx cy (P j)) s (group_point cx cy u) r).
proof. exact (little_endian_full_rejection_mass cx cy 5 2 1 P s &mem coordinates complete_model). qed.
