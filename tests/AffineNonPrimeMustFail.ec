require import AllCore Int IntDiv.
require import AffineAddition.

(* False: distinct x-coordinates alone do not suffice over a composite ring. *)
lemma nonzero_denominator_alone_implies_unique m ax ay bx byy rx ry lam rx2 ry2 lam2 :
  (bx-ax) %% m <> 0 =>
  affine_equations m ax ay bx byy rx ry lam =>
  affine_equations m ax ay bx byy rx2 ry2 lam2 => eqm m rx rx2.
proof. rewrite /affine_equations. smt(). qed.
