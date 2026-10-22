require import AllCore Int IntDiv StdOrder.
require import AffineAddition AffineDoubling AffineComplete.

(* Tangent slope 13: twice (5,1) is (6,3) on y^2=x^3+2x+2 over F_17. *)
lemma doubling_example :
  on_affine_curve 17 2 2 5 1 /\ doubling_equations 17 2 5 1 6 3 13 /\
  complete_constraints 17 2 (false,5,1) (false,5,1) (false,6,3) 13 /\
  on_affine_curve 17 2 2 6 3.
proof.
rewrite /on_affine_curve /curve_residual /doubling_equations
  /complete_constraints /point_bounded /=. smt().
qed.

lemma complete_distinct_inputs :
  complete_constraints 17 2 (false,5,1) (false,6,3) (false,10,6) 2.
proof. rewrite /complete_constraints /point_bounded /affine_equations /=. smt(). qed.

(* Both identity branches and identity plus identity. *)
lemma identity_branches :
  complete_constraints 17 2 infinity (false,5,1) (false,5,1) 0 /\
  complete_constraints 17 2 (false,5,1) infinity (false,5,1) 0 /\
  complete_constraints 17 2 infinity infinity infinity 0.
proof.
rewrite /complete_constraints /point_bounded /normalize_point /infinity /=. smt().
qed.

(* Final correction may cancel the accumulator exactly. *)
lemma inverse_pair_returns_identity :
  complete_constraints 17 2 (false,5,1) (false,5,16) infinity 0 /\
  forall rx ry lam, !complete_constraints 17 2 (false,5,1) (false,5,16) (false,rx,ry) lam.
proof. rewrite /complete_constraints /point_bounded /infinity /=. smt(). qed.

(* A genuine 2-torsion point on the nonsingular curve y^2=x^3+2x over F_17.
   Raw complete arithmetic covers it even though the MSM subgroup excludes it. *)
lemma zero_y_doubling :
  on_affine_curve 17 2 0 0 0 /\
  complete_constraints 17 2 (false,0,0) (false,0,0) infinity 0 /\
  forall rx ry lam, !doubling_equations 17 2 0 0 rx ry lam.
proof.
rewrite /on_affine_curve /curve_residual /complete_constraints /point_bounded
  /infinity /doubling_equations /=. smt().
qed.

(* Noncanonical input representatives are allowed, but outputs are bounded. *)
lemma representative_boundaries :
  complete_constraints 17 2 (false,22,18) (false,6,3) (false,10,6) 2 /\
  !complete_constraints 17 2 (false,5,1) (false,6,3) (false,27,6) 2 /\
  !complete_constraints 17 2 infinity infinity (true,1,0) 0.
proof.
rewrite /complete_constraints /point_bounded /normalize_point /infinity /affine_equations /=.
smt().
qed.

(* Equal x alone is not enough when the supplied inputs are off curve. *)
lemma invalid_equal_x_inputs_rejected : forall r lam,
  !complete_constraints 17 2 (false,0,0) (false,0,1) r lam.
proof. rewrite /complete_constraints /=. smt(). qed.

(* Dropping the tangent-denominator premise destroys uniqueness. This
   algebraic example is singular; no nonsingular-curve premise is claimed
   by the standalone equation-uniqueness theorem. *)
lemma zero_denominator_nonunique :
  doubling_equations 17 0 0 0 0 0 0 /\
  doubling_equations 17 0 0 0 1 16 1 /\ 0 %% 17 <> 1 %% 17.
proof. rewrite /doubling_equations. smt(). qed.
