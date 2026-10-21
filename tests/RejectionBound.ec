require import AllCore Distr.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
 MSM_TableConstruction MSM_WithTable MSM_RejectionBound.

(* Nonzero base points are essential: this builder deliberately rejects them. *)
lemma zero_base_rejects P s &m :
 (exists j, 0 <= j < l /\ P j = idR) =>
 Pr[SampledConstructedMSM.run(P,s) @ &m : !res.`1] = 1%r.
proof.
move=> Hzero. rewrite sampled_rejection_mass.
have ->: (fun u => !construction_accepts P s u) = (fun (_ : R) => true).
+ apply fun_ext. rewrite /construction_accepts /table_safe /row_safe. smt().
exact r_distr_ll.
qed.

(* Invalid scalar encodings cannot be covered by the small-rejection bound. *)
lemma invalid_windows_reject P s &m : ! valid_windows s =>
 Pr[SampledConstructedMSM.run(P,s) @ &m : !res.`1] = 1%r.
proof.
move=> Hbad. rewrite sampled_rejection_mass.
have ->: (fun u => !construction_accepts P s u) = (fun (_ : R) => true).
+ apply fun_ext. rewrite /construction_accepts. smt().
exact r_distr_ll.
qed.

lemma zero_scalar_event_mass :
 mu r_distr (fun u => 0 *** u = idR) = 1%r.
proof.
have ->: (fun (u : R) => 0 *** u = idR) = (fun (_ : R) => true)
 by apply fun_ext; smt(zero_mul).
exact r_distr_ll.
qed.

lemma zero_scalar_not_invertible P : P <> idR => ! scalar_invertible 0.
proof. rewrite /scalar_invertible. smt(zero_mul mul_idr). qed.
