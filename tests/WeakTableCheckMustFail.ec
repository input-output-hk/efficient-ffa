require import AllCore.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract MSM_TableConstruction.

(* The paper's old x(P) != x(V) check does not protect every row step. *)
lemma weak_table_check_suffices P V :
 P <> idR => xdiff P V => row_safe P V 4.
proof. smt(notxdiff). qed.
