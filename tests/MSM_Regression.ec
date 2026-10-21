require import AllCore MultiScalarMul_Abstract MultiScalarMul_Abstract_Setup.

(* Identity remains fixed by doubling; it must not satisfy admissibility. *)
lemma identity_doubling n : 2 ^ n *** idR = idR.
proof. apply mul_idr. qed.

lemma identity_rejected P s : ! u_check idR P s.
proof. rewrite /u_check mul_idr. trivial. qed.

lemma zero_initial_rejected U P s :
  l *** U = idR => ! u_check U P s.
proof. smt(u_check_initial). qed.

lemma selected_identity_rejected U P s j i :
  0 <= j < l => 0 <= i < T =>
  perfect_table_pure P U j (s j i) = idR =>
  ! u_check U P s.
proof. smt(u_check_for_table). qed.

lemma invalid_window_rejected U P s j i :
  0 <= j < l => 0 <= i < T =>
  ! (0 <= s j i < 2 ^ w) =>
  ! u_check U P s.
proof. rewrite /u_check. smt(). qed.
