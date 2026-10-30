require import AllCore Int IntDiv StdOrder.
require import AffineAddition.

(* Tangent formulas. Primality and the nonzero tangent denominator remain
   explicit premises; these definitions do not assume a group model. *)
op doubling_slope m ca ax ay = affine_slope m 0 0 (2*ay) (3*ax*ax+ca).
op doubling_equations m ca ax ay rx ry lam =
  (3*ax*ax+ca-lam*(2*ay)) %% m = 0 /\
  (ax+ax+rx-lam*lam) %% m = 0 /\
  (-ry-ay-lam*(rx-ax)) %% m = 0.

lemma doubling_equationsE m ca ax ay rx ry lam :
  doubling_equations m ca ax ay rx ry lam <=>
  eqm m (lam*(2*ay)) (3*ax*ax+ca) /\
  eqm m rx (affine_x ax ax lam) /\
  eqm m ry (affine_y ax ay rx lam).
proof.
rewrite /doubling_equations /affine_x /affine_y.
have E1 : ax+ax+rx-lam*lam = rx-(lam*lam-ax-ax) by ring.
have E2 : -ry-ay-lam*(rx-ax) = (lam*(ax-rx)-ay)-ry by ring.
rewrite E1 E2 !congr_zero. smt().
qed.

lemma doubling_slope_valid m ca ax ay :
  prime m => (2*ay) %% m <> 0 =>
  eqm m ((doubling_slope m ca ax ay)*(2*ay)) (3*ax*ax+ca).
proof.
move=> Hp Hnz.
have H := affine_slope_valid m 0 0 (2*ay) (3*ax*ax+ca) Hp _.
+ smt().
move: H. rewrite /doubling_slope /affine_slope /=. trivial.
qed.

lemma doubling_slope_unique m ca ax ay lam :
  prime m => (2*ay) %% m <> 0 =>
  eqm m (lam*(2*ay)) (3*ax*ax+ca) => eqm m lam (doubling_slope m ca ax ay).
proof.
move=> Hp Hnz Hs.
have Hcan := doubling_slope_valid m ca ax ay Hp Hnz.
apply (eqmZI m lam (doubling_slope m ca ax ay) (2*ay)
  (gt1_prime m Hp) (prime_coprime m Hp (2*ay) Hnz)).
smt().
qed.

lemma doubling_witness_exists m ca ax ay :
  prime m => (2*ay) %% m <> 0 =>
  let lam = doubling_slope m ca ax ay in
  let rx = affine_x ax ax lam in
  doubling_equations m ca ax ay rx (affine_y ax ay rx lam) lam.
proof.
move=> Hp Hnz. simplify. rewrite doubling_equationsE.
smt(doubling_slope_valid).
qed.

lemma doubling_equations_unique m ca ax ay rx ry lam :
  prime m => (2*ay) %% m <> 0 =>
  doubling_equations m ca ax ay rx ry lam =>
  let sl = doubling_slope m ca ax ay in
  let sx = affine_x ax ax sl in
  eqm m lam sl /\ eqm m rx sx /\ eqm m ry (affine_y ax ay sx sl).
proof.
move=> Hp Hnz. rewrite doubling_equationsE.
move=> [Hs [Hx Hy]]. simplify.
have Hl := doubling_slope_unique m ca ax ay lam Hp Hnz Hs.
have Hxx := affine_x_congr m ax ax lam (doubling_slope m ca ax ay) Hl.
have Hrx : eqm m rx (affine_x ax ax (doubling_slope m ca ax ay)) by smt().
have Hyy := affine_y_congr m ax ay rx (affine_x ax ax (doubling_slope m ca ax ay))
  lam (doubling_slope m ca ax ay) Hrx Hl.
smt().
qed.

lemma doubling_curve_identity ca cb ax ay lam :
  let rx = affine_x ax ax lam in
  let ry = affine_y ax ay rx lam in
  curve_residual ca cb rx ry = curve_residual ca cb ax ay -
    (rx-ax)*(3*ax*ax+ca-lam*(2*ay)).
proof. rewrite /affine_x /affine_y /curve_residual /=. ring. qed.

lemma doubling_formula_on_curve m ca cb ax ay lam :
  on_affine_curve m ca cb ax ay => (3*ax*ax+ca-lam*(2*ay)) %% m = 0 =>
  let rx = affine_x ax ax lam in on_affine_curve m ca cb rx (affine_y ax ay rx lam).
proof.
rewrite /on_affine_curve. move=> Ha Hs. simplify.
have Hprod := mod_product_zero m _ (affine_x ax ax lam-ax) Hs.
have Hdiff := mod_difference_zero m _ _ Ha Hprod.
have E := doubling_curve_identity ca cb ax ay lam.
move: E. simplify. move=> E. smt().
qed.

lemma doubling_equations_on_curve m ca cb ax ay rx ry lam :
  on_affine_curve m ca cb ax ay =>
  doubling_equations m ca ax ay rx ry lam => on_affine_curve m ca cb rx ry.
proof.
move=> Ha Heq.
move: (Heq). rewrite doubling_equationsE. move=> [Hs [Hx Hy]].
have Hs0 : (3*ax*ax+ca-lam*(2*ay)) %% m = 0
  by move: Heq; rewrite /doubling_equations; smt().
have Hcurve := doubling_formula_on_curve m ca cb ax ay lam Ha Hs0.
have Hyy := affine_y_congr m ax ay rx (affine_x ax ax lam) lam lam Hx (eqm_refl m lam).
have Hry : eqm m ry (affine_y ax ay (affine_x ax ax lam) lam) by smt().
have Hres := curve_residual_congr m ca cb rx ry (affine_x ax ax lam)
  (affine_y ax ay (affine_x ax ax lam) lam) Hx Hry.
move: Hcurve. rewrite /on_affine_curve. smt().
qed.

lemma doubling_equations_residues m ca ax ay rx ry lam :
  doubling_equations m ca ax ay rx ry lam =>
  doubling_equations m ca ax ay (rx %% m) (ry %% m) (lam %% m).
proof.
rewrite !doubling_equationsE. move=> [Hs [Hx Hy]].
have Hl : eqm m (lam %% m) lam by smt(modz_mod).
have Hrx : eqm m (rx %% m) rx by smt(modz_mod).
have Hry : eqm m (ry %% m) ry by smt(modz_mod).
have Hs' := eqmM m (lam %% m) lam (2*ay) (2*ay) Hl (eqm_refl m (2*ay)).
have Hx' := affine_x_congr m ax ax (lam %% m) lam Hl.
have Hy' := affine_y_congr m ax ay (rx %% m) rx (lam %% m) lam Hrx Hl.
smt().
qed.

lemma doubling_bounded_witnesses m ca ax ay :
  prime m => (2*ay) %% m <> 0 =>
  exists rx ry lam, 0 <= rx < m /\ 0 <= ry < m /\ 0 <= lam < m /\
    doubling_equations m ca ax ay rx ry lam.
proof.
move=> Hp Hnz.
pose sl := doubling_slope m ca ax ay.
pose sx := affine_x ax ax sl.
pose sy := affine_y ax ay sx sl.
have Heq : doubling_equations m ca ax ay sx sy sl
  by exact (doubling_witness_exists m ca ax ay Hp Hnz).
have Hres := doubling_equations_residues m ca ax ay sx sy sl Heq.
exists (sx %% m) (sy %% m) (sl %% m).
smt(modz_ge0 ltz_pmod gt0_prime).
qed.
