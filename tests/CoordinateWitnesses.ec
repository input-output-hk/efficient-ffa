require import AllCore Int IntDiv StdOrder.
require import AffineAddition MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
  MSM_TableConstruction MSM_TableConstraints MSM_CoordinateWitnesses.

(* A concrete short-Weierstrass addition over F_17:
   (5,1)+(6,3)=(10,6) on y^2=x^3+2x+2, with slope 2. *)
lemma affine_addition_example :
  on_affine_curve 17 2 2 5 1 /\ on_affine_curve 17 2 2 6 3 /\
  affine_equations 17 5 1 6 3 10 6 2 /\ on_affine_curve 17 2 2 10 6.
proof. rewrite /on_affine_curve /curve_residual /affine_equations. smt(). qed.

(* A nonzero denominator is insufficient over a composite modulus. *)
lemma composite_modulus_nonunique :
  (2-0) %% 6 <> 0 /\
  affine_equations 6 0 0 2 0 4 0 0 /\
  affine_equations 6 0 0 2 0 1 3 3 /\ 4 %% 6 <> 1 %% 6.
proof. rewrite /affine_equations. smt(). qed.

(* Over a prime field, equal inputs still invalidate slope uniqueness.
   The two satisfying outputs need not even lie on the input curve. *)
lemma equal_x_nonunique :
  affine_equations 17 5 1 5 1 7 16 0 /\
  affine_equations 17 5 1 5 1 8 13 1 /\ 7 %% 17 <> 8 %% 17 /\
  ! on_affine_curve 17 2 2 7 16.
proof. rewrite /affine_equations /on_affine_curve /curve_residual. smt(). qed.

(* Width >=2 is essential for row_safe to imply the initial check: a
   one-entry row does not execute an addition at all. Actual width is 2^w. *)
lemma one_entry_boundary x y m P : P <> idR =>
  row_safe P P 1 /\
  forall entries slopes, ! accepted_table_row x y m P P 1 entries slopes.
proof.
move=> Hp. rewrite row_safe1 /accepted_table_row.
smt(op_inv op_id mod0z).
qed.

(* The inverse-pair example is unsatisfiable, not an accepted bad table. *)
lemma inverse_pair_unsatisfiable : forall rx ry lam,
  ! affine_equations 17 5 16 5 1 rx ry lam.
proof. rewrite /affine_equations. smt(). qed.
