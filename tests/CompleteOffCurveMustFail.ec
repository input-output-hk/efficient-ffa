require import AllCore Int IntDiv AffineComplete.

(* EXPECTED FAILURE: totality needs on-curve input premises. *)
lemma off_curve_inputs_have_witnesses : exists r lam,
  complete_constraints 17 2 (false,0,0) (false,0,1) r lam.
proof. smt(complete_witness_exists). qed.
