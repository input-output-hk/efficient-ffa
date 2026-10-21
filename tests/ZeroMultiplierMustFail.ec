require import AllCore.
require import MultiScalarMul_Abstract_Setup MSM_RejectionBound.

(* invertmeP applies only to nonzero scalars below the stated bound. *)
lemma zero_scalar_invertible : scalar_invertible 0.
proof. rewrite /scalar_invertible. smt(invertmeP). qed.
