require import AllCore Int IntDiv AffineDoubling.

(* EXPECTED FAILURE: the nonzero tangent denominator is essential. *)
lemma unrestricted_doubling_unique : forall rx ry lam,
  doubling_equations 17 0 0 0 rx ry lam => eqm 17 rx 0.
proof. smt(doubling_equations_unique). qed.
