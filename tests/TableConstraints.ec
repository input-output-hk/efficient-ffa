require import AllCore Int IntDiv StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
  MSM_TableConstruction MSM_TableConstraints.

(* The old counterexample is an unsatisfiable table, not an accepted wrong
   result: the constraints themselves reject V=2P for a four-entry row. *)
lemma two_p_constraint_row_impossible x y m P entries slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  ! accepted_table_row x y m P (2 *** P) 4 entries slopes.
proof.
move=> Hcoord Hcorrect.
have H := accepted_table_row_safe x y m P (2 *** P) 4 entries slopes Hcoord Hcorrect.
have Heq := table_entry_eq_mul P (2 *** P) 2 0.
move: H. rewrite /row_safe. smt(zero_mul).
qed.

(* With y(P)=0 the output-exclusion argument is false: zero coordinates
   and zero slope satisfy every equation with output P. Thus the explicit
   no-2-torsion coordinate hypothesis cannot simply be dropped. *)
lemma zero_y_allows_base_output P : P <> idR =>
  incomplete_constraints (fun _ => 0) (fun _ => 0) 5 P P P 0.
proof. rewrite /incomplete_constraints /slope_constraint. smt(mod0z). qed.

(* Nonzero y alone does not make an isolated addition reject equal inputs.
   The table's initial check and repeated-base chain are essential. This is
   a coordinate-equation example, not a concrete curve-group instance. *)
lemma equal_inputs_can_satisfy_constraints P :
  P <> idR => P <> -P =>
  incomplete_constraints (fun _ => 0) (fun a => if a=P then 1 else -1)
    5 P P (-P) 0 /\
  (2 * (fun a => if a=P then 1 else -1) P) %% 5 <> 0 /\
  ! xdiff P P.
proof.
move=> Hp Hneg.
have Hnz : -P <> idR by smt(op_inv op_id).
rewrite /incomplete_constraints /slope_constraint /xdiff.
smt(mod0z pmod_small).
qed.
