require import AllCore AffineComplete MSM_CoordinateTrace.

(* EXPECTED FAILURE: the uncorrected accumulator 3P cannot also be the
   output after subtracting the nonzero initial offset 2P. *)
lemma omit_final_correction :
  complete_step 17 2 (false,10,6) (false,6,14) (false,10,6).
proof. rewrite /complete_step /complete_constraints /AffineAddition.affine_equations. smt(). qed.
