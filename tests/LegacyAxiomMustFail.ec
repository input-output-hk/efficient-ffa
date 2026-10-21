require import AllCore MultiScalarMul_Abstract_Setup.

(* EXPECTED FAILURE. The original unconditional axiom proves this theorem.
   Rejection catches that specific regression; it is not a consistency proof. *)
lemma legacy_axiom_would_prove_false : false.
proof.
have bad := no_order_two_elems idR 1.
have zero := mul_idr (2 ^ 1).
smt().
qed.
