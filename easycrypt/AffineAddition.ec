require import AllCore Int IntDiv StdOrder.

(* Integer representatives of the affine formulas over Z/mZ. The modulus
   and nonzero denominator are theorem premises, not global axioms. *)
op affine_slope m ax ay bx byy = (byy-ay) * invm (bx-ax) m.
op affine_x (ax bx lam : int) = lam*lam-ax-bx.
op affine_y (ax ay rx lam : int) = lam*(ax-rx)-ay.

op affine_equations m ax ay bx byy rx ry lam =
  (byy-ay-lam*(bx-ax)) %% m = 0 /\
  (ax+bx+rx-lam*lam) %% m = 0 /\
  (-ry-ay-lam*(rx-ax)) %% m = 0.

lemma congr_zero m a b : (a-b) %% m = 0 <=> eqm m a b.
proof. by rewrite -dvdzE eqz_mod_dvd. qed.

lemma affine_equationsE m ax ay bx byy rx ry lam :
  affine_equations m ax ay bx byy rx ry lam <=>
  eqm m (lam*(bx-ax)) (byy-ay) /\
  eqm m rx (affine_x ax bx lam) /\
  eqm m ry (affine_y ax ay rx lam).
proof.
rewrite /affine_equations /affine_x /affine_y.
have E1 : ax+bx+rx-lam*lam = rx-(lam*lam-ax-bx) by ring.
have E2 : -ry-ay-lam*(rx-ax) = (lam*(ax-rx)-ay)-ry by ring.
rewrite E1 E2 !congr_zero. smt().
qed.

lemma affine_slope_valid m ax ay bx byy :
  prime m => (bx-ax) %% m <> 0 =>
  eqm m ((affine_slope m ax ay bx byy)*(bx-ax)) (byy-ay).
proof.
move=> Hprime Hnz.
have Hinv := eqmV m (bx-ax) (gt1_prime m Hprime) (prime_coprime m Hprime (bx-ax) Hnz).
have H := eqmM m (byy-ay) (byy-ay) ((bx-ax)*invm (bx-ax) m) 1 (eqm_refl m (byy-ay)) Hinv.
rewrite /affine_slope.
have E : ((byy-ay)*invm (bx-ax) m)*(bx-ax) = (byy-ay)*((bx-ax)*invm (bx-ax) m) by ring.
smt().
qed.

lemma affine_witness_exists m ax ay bx byy :
  prime m => (bx-ax) %% m <> 0 =>
  let lam = affine_slope m ax ay bx byy in
  let rx = affine_x ax bx lam in
  affine_equations m ax ay bx byy rx (affine_y ax ay rx lam) lam.
proof.
move=> Hprime Hnz. simplify. rewrite affine_equationsE.
smt(affine_slope_valid).
qed.

lemma affine_slope_unique m ax ay bx byy lam :
  prime m => (bx-ax) %% m <> 0 =>
  eqm m (lam*(bx-ax)) (byy-ay) =>
  eqm m lam (affine_slope m ax ay bx byy).
proof.
move=> Hprime Hnz Hs.
have Hcanonical := affine_slope_valid m ax ay bx byy Hprime Hnz.
apply (eqmZI m lam (affine_slope m ax ay bx byy) (bx-ax)
  (gt1_prime m Hprime) (prime_coprime m Hprime (bx-ax) Hnz)).
smt().
qed.

lemma affine_x_congr m ax bx l1 l2 : eqm m l1 l2 =>
  eqm m (affine_x ax bx l1) (affine_x ax bx l2).
proof.
move=> H. rewrite /affine_x.
apply eqmB; last exact (eqm_refl m bx).
apply eqmB; last exact (eqm_refl m ax).
exact (eqmM m l1 l2 l1 l2 H H).
qed.

lemma affine_y_congr m ax ay x1 x2 l1 l2 :
  eqm m x1 x2 => eqm m l1 l2 =>
  eqm m (affine_y ax ay x1 l1) (affine_y ax ay x2 l2).
proof.
move=> Hx Hl. rewrite /affine_y.
apply eqmB; last exact (eqm_refl m ay).
apply eqmM; first exact Hl.
apply eqmB; [exact (eqm_refl m ax) | exact Hx].
qed.

(* No curve-membership premise on the witnessed output is needed here. *)
lemma affine_equations_unique m ax ay bx byy rx ry lam :
  prime m => (bx-ax) %% m <> 0 =>
  affine_equations m ax ay bx byy rx ry lam =>
  let sl = affine_slope m ax ay bx byy in
  let sx = affine_x ax bx sl in
  eqm m lam sl /\ eqm m rx sx /\ eqm m ry (affine_y ax ay sx sl).
proof.
move=> Hprime Hnz. rewrite affine_equationsE.
move=> [Hs [Hx Hy]]. simplify.
have Hl := affine_slope_unique m ax ay bx byy lam Hprime Hnz Hs.
have Hxx := affine_x_congr m ax bx lam (affine_slope m ax ay bx byy) Hl.
have Hrx : eqm m rx (affine_x ax bx (affine_slope m ax ay bx byy)) by smt().
have Hyy := affine_y_congr m ax ay rx (affine_x ax bx (affine_slope m ax ay bx byy))
  lam (affine_slope m ax ay bx byy) Hrx Hl.
smt().
qed.

(* Curve membership follows from the safe formulas; it is not assumed for
   the witnessed output. The argument does not require nonsingularity. *)
op curve_residual (ca cb px py : int) = py*py-px*px*px-ca*px-cb.
op on_affine_curve m ca cb px py = curve_residual ca cb px py %% m = 0.

lemma mod_add_zero m a b : a %% m = 0 => b %% m = 0 => (a+b) %% m = 0.
proof. move=> Ha Hb. rewrite -modzDm Ha Hb. smt(mod0z). qed.

lemma mod_difference_zero m a b : a %% m = 0 => b %% m = 0 => (a-b) %% m = 0.
proof. move=> Ha Hb. rewrite -modzBm Ha Hb. smt(mod0z). qed.

lemma mod_product_zero m a b : a %% m = 0 => (b*a) %% m = 0.
proof. move=> Ha. rewrite -modzMmr Ha. smt(mod0z). qed.

lemma affine_curve_identity ca cb ax ay bx byy lam :
  let rx = affine_x ax bx lam in
  let ry = affine_y ax ay rx lam in
  (bx-ax)*curve_residual ca cb rx ry =
  (bx-ax)*curve_residual ca cb ax ay +
  (rx-ax)*(curve_residual ca cb bx byy - curve_residual ca cb ax ay -
    (byy-ay-lam*(bx-ax))*(byy+ay+lam*(bx-ax))).
proof. rewrite /affine_x /affine_y /curve_residual /=. ring. qed.

lemma affine_formula_on_curve m ca cb ax ay bx byy lam :
  prime m => (bx-ax) %% m <> 0 =>
  on_affine_curve m ca cb ax ay => on_affine_curve m ca cb bx byy =>
  (byy-ay-lam*(bx-ax)) %% m = 0 =>
  let rx = affine_x ax bx lam in
  on_affine_curve m ca cb rx (affine_y ax ay rx lam).
proof.
move=> Hprime Hnz Ha Hb Hs. simplify.
move: Ha Hb. rewrite /on_affine_curve. move=> Ha Hb.
have Hab := mod_difference_zero m _ _ Hb Ha.
have Hsprod := mod_product_zero m _ (byy+ay+lam*(bx-ax)) Hs.
have E : (byy+ay+lam*(bx-ax))*(byy-ay-lam*(bx-ax)) =
  (byy-ay-lam*(bx-ax))*(byy+ay+lam*(bx-ax)) by ring.
move: Hsprod. rewrite E. move=> Hsprod.
have Hd := mod_difference_zero m _ _ Hab Hsprod.
have Hright := mod_product_zero m _ (affine_x ax bx lam-ax) Hd.
have Hleft := mod_product_zero m _ (bx-ax) Ha.
have Hsum := mod_add_zero m _ _ Hleft Hright.
have Ecurve := affine_curve_identity ca cb ax ay bx byy lam.
move: Ecurve. simplify. move=> Ecurve.
have Hzero : eqm m (curve_residual ca cb (affine_x ax bx lam)
  (affine_y ax ay (affine_x ax bx lam) lam)) 0.
+ apply (eqmZI m _ 0 (bx-ax) (gt1_prime m Hprime)
    (prime_coprime m Hprime (bx-ax) Hnz)). smt(mod0z).
smt(mod0z).
qed.

lemma curve_residual_congr m ca cb x1 y1 x2 y2 :
  eqm m x1 x2 => eqm m y1 y2 =>
  eqm m (curve_residual ca cb x1 y1) (curve_residual ca cb x2 y2).
proof.
move=> Hx Hy. rewrite /curve_residual.
apply eqmB; last exact (eqm_refl m cb).
apply eqmB; last apply eqmM; try exact (eqm_refl m ca); try exact Hx.
apply eqmB.
+ exact (eqmM m y1 y2 y1 y2 Hy Hy).
+ apply eqmM; last exact Hx. exact (eqmM m x1 x2 x1 x2 Hx Hx).
qed.

lemma affine_equations_on_curve m ca cb ax ay bx byy rx ry lam :
  prime m => (bx-ax) %% m <> 0 =>
  on_affine_curve m ca cb ax ay => on_affine_curve m ca cb bx byy =>
  affine_equations m ax ay bx byy rx ry lam =>
  on_affine_curve m ca cb rx ry.
proof.
move=> Hprime Hnz Ha Hb Heq.
move: (Heq). rewrite affine_equationsE. move=> [Hs [Hx Hy]].
have Hs0 : (byy-ay-lam*(bx-ax)) %% m = 0 by move: Heq; rewrite /affine_equations; smt().
have Hcurve := affine_formula_on_curve m ca cb ax ay bx byy lam Hprime Hnz Ha Hb Hs0.
have Hyy := affine_y_congr m ax ay rx (affine_x ax bx lam) lam lam Hx (eqm_refl m lam).
have Hry : eqm m ry (affine_y ax ay (affine_x ax bx lam) lam) by smt().
have Hres := curve_residual_congr m ca cb rx ry (affine_x ax bx lam)
  (affine_y ax ay (affine_x ax bx lam) lam) Hx Hry.
move: Hcurve. rewrite /on_affine_curve. smt().
qed.

lemma affine_equations_residues m ax ay bx byy rx ry lam :
  affine_equations m ax ay bx byy rx ry lam =>
  affine_equations m ax ay bx byy (rx %% m) (ry %% m) (lam %% m).
proof.
rewrite !affine_equationsE. move=> [Hs [Hx Hy]].
have Hl : eqm m (lam %% m) lam by smt(modz_mod).
have Hrx : eqm m (rx %% m) rx by smt(modz_mod).
have Hry : eqm m (ry %% m) ry by smt(modz_mod).
have Hs' := eqmM m (lam %% m) lam (bx-ax) (bx-ax) Hl (eqm_refl m (bx-ax)).
have Hx' := affine_x_congr m ax bx (lam %% m) lam Hl.
have Hy' := affine_y_congr m ax ay (rx %% m) rx (lam %% m) lam Hrx Hl.
smt().
qed.

lemma affine_bounded_witnesses m ax ay bx byy :
  prime m => (bx-ax) %% m <> 0 =>
  exists rx ry lam, 0 <= rx < m /\ 0 <= ry < m /\ 0 <= lam < m /\
    affine_equations m ax ay bx byy rx ry lam.
proof.
move=> Hprime Hnz.
pose sl := affine_slope m ax ay bx byy.
pose sx := affine_x ax bx sl.
pose sy := affine_y ax ay sx sl.
have Heq : affine_equations m ax ay bx byy sx sy sl
  by exact (affine_witness_exists m ax ay bx byy Hprime Hnz).
have Hres := affine_equations_residues m ax ay bx byy sx sy sl Heq.
exists (sx %% m) (sy %% m) (sl %% m).
smt(modz_ge0 ltz_pmod gt0_prime).
qed.

lemma affine_equations_slope_residue m ax ay bx byy rx ry lam :
  affine_equations m ax ay bx byy rx ry lam =>
  affine_equations m ax ay bx byy rx ry (lam %% m).
proof.
rewrite !affine_equationsE. move=> [Hs [Hx Hy]].
have Hl : eqm m (lam %% m) lam by smt(modz_mod).
have Hs' := eqmM m (lam %% m) lam (bx-ax) (bx-ax) Hl (eqm_refl m (bx-ax)).
have Hx' := affine_x_congr m ax bx (lam %% m) lam Hl.
have Hy' := affine_y_congr m ax ay rx rx (lam %% m) lam (eqm_refl m rx) Hl.
smt().
qed.
