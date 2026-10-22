require import AllCore Int IntDiv StdOrder.
require import AffineAddition AffineDoubling.

(* Infinity is an explicit Boolean tag, never an invented affine point.
   Accepted outputs use canonical coordinates and the unique encoding (true,0,0)
   for infinity. Inputs may use any integer representatives. *)
type coordinate_point = bool * int * int.
op infinity : coordinate_point = (true,0,0).
op normalize_point m (p : coordinate_point) : coordinate_point =
  if p.`1 then infinity else (false,p.`2 %% m,p.`3 %% m).
op point_bounded m (p : coordinate_point) =
  if p.`1 then p = infinity else 0 <= p.`2 < m /\ 0 <= p.`3 < m.
op point_on_curve m ca cb (p : coordinate_point) =
  p.`1 \/ on_affine_curve m ca cb p.`2 p.`3.

op complete_constraints m ca (a b r : coordinate_point) lam =
  point_bounded m r /\ 0 <= lam < m /\
  if a.`1 then r = normalize_point m b /\ lam=0
  else if b.`1 then r = normalize_point m a /\ lam=0
  else if (b.`2-a.`2) %% m <> 0 then
    !r.`1 /\ affine_equations m a.`2 a.`3 b.`2 b.`3 r.`2 r.`3 lam
  else if (b.`3+a.`3) %% m = 0 then r=infinity /\ lam=0
  else eqm m b.`3 a.`3 /\ (2*a.`3) %% m <> 0 /\ !r.`1 /\
    doubling_equations m ca a.`2 a.`3 r.`2 r.`3 lam.

(* Deterministic affine formula, with complete case splitting. This is an
   arithmetic specification, not yet a proof of an elliptic-curve group law. *)
op complete_add m ca (a b : coordinate_point) : coordinate_point =
  if a.`1 then normalize_point m b
  else if b.`1 then normalize_point m a
  else if (b.`2-a.`2) %% m <> 0 then
    let sl = affine_slope m a.`2 a.`3 b.`2 b.`3 in
    let sx = affine_x a.`2 b.`2 sl in
    normalize_point m (false,sx,affine_y a.`2 a.`3 sx sl)
  else if (b.`3+a.`3) %% m = 0 then infinity
  else let sl = doubling_slope m ca a.`2 a.`3 in
    let sx = affine_x a.`2 a.`2 sl in
    normalize_point m (false,sx,affine_y a.`2 a.`3 sx sl).

lemma normalize_point_bounded m p : 0 < m => point_bounded m (normalize_point m p).
proof.
move=> Hm. rewrite /normalize_point. case (p.`1).
+ move=> H. by rewrite /point_bounded /infinity /=.
move=> H. rewrite /point_bounded /=.
have Hx0 := modz_ge0 p.`2 m.
have Hy0 := modz_ge0 p.`3 m.
have Hxm := ltz_pmod p.`2 m Hm.
have Hym := ltz_pmod p.`3 m Hm.
smt().
qed.

lemma normalize_point_on_curve m ca cb p :
  point_on_curve m ca cb p => point_on_curve m ca cb (normalize_point m p).
proof.
rewrite /point_on_curve /normalize_point /infinity.
case (p.`1); first smt(). move=> Hfin Ha.
have Hx : eqm m (p.`2 %% m) p.`2 by smt(modz_mod).
have Hy : eqm m (p.`3 %% m) p.`3 by smt(modz_mod).
have H := curve_residual_congr m ca cb (p.`2 %% m) (p.`3 %% m) p.`2 p.`3 Hx Hy.
move: Ha. rewrite /on_affine_curve. smt().
qed.

(* For two on-curve points with equal x, a nonzero y-sum forces equal y.
   Hence the nonvertical equal-x branch really is a doubling branch. *)
lemma equal_x_doubling_branch m ca cb ax ay bx byy :
  prime m => on_affine_curve m ca cb ax ay => on_affine_curve m ca cb bx byy =>
  (bx-ax) %% m = 0 => (byy+ay) %% m <> 0 =>
  eqm m byy ay /\ (2*ay) %% m <> 0.
proof.
move=> Hp Ha Hb Hx Hsum.
have Hxx : eqm m bx ax by smt(congr_zero).
have Hres := curve_residual_congr m ca cb bx byy ax byy Hxx (eqm_refl m byy).
have Hsame : on_affine_curve m ca cb ax byy
  by move: Hb; rewrite /on_affine_curve; smt().
have Hzero : ((byy-ay)*(byy+ay)) %% m = 0.
+ have E : (byy-ay)*(byy+ay) = curve_residual ca cb ax byy - curve_residual ca cb ax ay
    by rewrite /curve_residual; ring.
  rewrite E. apply mod_difference_zero; move: Ha Hsame; rewrite /on_affine_curve; smt().
have Hdiff : eqm m (byy-ay) 0.
+ apply (eqmZI m (byy-ay) 0 (byy+ay) (gt1_prime m Hp)
    (prime_coprime m Hp (byy+ay) Hsum)). smt(mod0z).
have Hy : eqm m byy ay by smt(congr_zero mod0z).
have Hplus := eqmD m byy ay ay ay Hy (eqm_refl m ay).
smt().
qed.

lemma complete_witness_exists m ca cb a b :
  prime m => point_on_curve m ca cb a => point_on_curve m ca cb b =>
  exists r lam, complete_constraints m ca a b r lam.
proof.
move=> Hp Ha Hb. have Hm : 0 < m by smt(gt0_prime).
case (a.`1).
+ move=> H. exists (normalize_point m b) 0.
  rewrite /complete_constraints H /=. smt(normalize_point_bounded).
move=> Hafin. case (b.`1).
+ move=> H. exists (normalize_point m a) 0.
  rewrite /complete_constraints Hafin H /=. smt(normalize_point_bounded).
move=> Hbfin. case ((b.`2-a.`2) %% m <> 0).
+ move=> Hdx.
  have [rx ry lam H] := affine_bounded_witnesses m a.`2 a.`3 b.`2 b.`3 Hp Hdx.
  exists (false,rx,ry) lam.
  rewrite /complete_constraints Hafin Hbfin Hdx /point_bounded /=. smt().
move=> Hdx. case ((b.`3+a.`3) %% m = 0).
+ move=> Hsum. exists infinity 0.
  rewrite /complete_constraints Hafin Hbfin Hdx Hsum /point_bounded /infinity /=. smt().
move=> Hsum.
have Hbranch := equal_x_doubling_branch m ca cb a.`2 a.`3 b.`2 b.`3 Hp _ _ _ Hsum.
+ move: Ha. rewrite /point_on_curve Hafin. smt().
+ move: Hb. rewrite /point_on_curve Hbfin. smt().
+ smt().
have [Hy Hden] := Hbranch.
have [rx ry lam H] := doubling_bounded_witnesses m ca a.`2 a.`3 Hp Hden.
exists (false,rx,ry) lam.
rewrite /complete_constraints Hafin Hbfin Hdx Hsum /point_bounded /=. smt().
qed.

lemma complete_constraints_sound m ca a b r lam :
  prime m => complete_constraints m ca a b r lam => r = complete_add m ca a b.
proof.
move=> Hp. rewrite /complete_constraints /complete_add.
move=> [Hbounded [Hlam H]].
case (a.`1); first smt(). move=> Ha.
case (b.`1); first smt(). move=> Hb.
case ((b.`2-a.`2) %% m <> 0).
+ move=> Hdx.
  have Heq : affine_equations m a.`2 a.`3 b.`2 b.`3 r.`2 r.`3 lam by smt().
  have Hu := affine_equations_unique m a.`2 a.`3 b.`2 b.`3 r.`2 r.`3 lam Hp Hdx Heq.
  move: Hbounded. rewrite /point_bounded /normalize_point /=. smt(modz_small gt0_prime).
move=> Hdx. case ((b.`3+a.`3) %% m = 0); first smt(). move=> Hsum.
have Hnz : (2*a.`3) %% m <> 0 by smt().
have Heq : doubling_equations m ca a.`2 a.`3 r.`2 r.`3 lam by smt().
have Hu := doubling_equations_unique m ca a.`2 a.`3 r.`2 r.`3 lam Hp Hnz Heq.
move: Hbounded. rewrite /point_bounded /normalize_point /=. smt(modz_small gt0_prime).
qed.

lemma complete_constraints_on_curve m ca cb a b r lam :
  prime m => point_on_curve m ca cb a => point_on_curve m ca cb b =>
  complete_constraints m ca a b r lam => point_on_curve m ca cb r.
proof.
move=> Hp Ha Hb. rewrite /complete_constraints. move=> [Hr [Hl H]].
case (a.`1); first smt(normalize_point_on_curve). move=> Hafin.
case (b.`1); first smt(normalize_point_on_curve). move=> Hbfin.
have Hac : on_affine_curve m ca cb a.`2 a.`3 by move: Ha; rewrite /point_on_curve Hafin; smt().
have Hbc : on_affine_curve m ca cb b.`2 b.`3 by move: Hb; rewrite /point_on_curve Hbfin; smt().
case ((b.`2-a.`2) %% m <> 0).
+ move=> Hdx. rewrite /point_on_curve.
  have Heq : affine_equations m a.`2 a.`3 b.`2 b.`3 r.`2 r.`3 lam by smt().
  smt(affine_equations_on_curve).
move=> Hdx. case ((b.`3+a.`3) %% m = 0).
+ move=> Hsum. rewrite /point_on_curve. have E : r = infinity by smt(). rewrite E /infinity /=. trivial.
move=> Hsum. rewrite /point_on_curve.
have Heq : doubling_equations m ca a.`2 a.`3 r.`2 r.`3 lam by smt().
smt(doubling_equations_on_curve).
qed.

lemma complete_add_has_witness m ca cb a b :
  prime m => point_on_curve m ca cb a => point_on_curve m ca cb b =>
  exists lam, complete_constraints m ca a b (complete_add m ca a b) lam.
proof.
move=> Hp Ha Hb.
have [r lam H] := complete_witness_exists m ca cb a b Hp Ha Hb.
have E := complete_constraints_sound m ca a b r lam Hp H.
exists lam. smt().
qed.

lemma complete_add_closed m ca cb a b :
  prime m => point_on_curve m ca cb a => point_on_curve m ca cb b =>
  point_on_curve m ca cb (complete_add m ca a b).
proof.
move=> Hp Ha Hb.
have [lam H] := complete_add_has_witness m ca cb a b Hp Ha Hb.
exact (complete_constraints_on_curve m ca cb a b (complete_add m ca a b) lam Hp Ha Hb H).
qed.
