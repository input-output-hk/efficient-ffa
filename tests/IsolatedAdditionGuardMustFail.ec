require import AllCore Int IntDiv.
require import MultiScalarMul_Abstract_Setup MSM_TableConstraints.

(* This does not follow from the equations for an isolated addition.
   Guard redundancy is a property of the repeated-base table chain. *)
lemma isolated_constraints_force_distinct_x x y m a p r lam :
  (2*y p) %% m <> 0 =>
  incomplete_constraints x y m a p r lam => xdiff a p.
proof. rewrite /incomplete_constraints /slope_constraint /xdiff. smt(). qed.
