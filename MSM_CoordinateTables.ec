require import AllCore Int IntDiv StdOrder.
require import AffineAddition AffineComplete MSM_CompleteCoordinates MSM_CoordinateTrace.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
  MSM_TableConstruction MSM_TableConstraints MSM_CoordinateWitnesses.

(* Exactly one unequal-x check per row. Later row steps carry only the
   original affine equations, finite flags and canonical witness ranges. *)
op coordinate_row m b p v (entries : int -> coordinate_point) =
  2 <= b /\ coordinate_safe m p v /\ entries 0=negate_point m v /\
  forall k, 0 <= k < b-1 => incomplete_step m (entries k) p (entries (k+1)).
op coordinate_tables m (P : int -> coordinate_point) v table =
  forall j, 0 <= j < l => coordinate_row m (2^w) (P j) v (table j).

lemma incomplete_output_not_base m a (b : coordinate_point) r : (2*b.`3) %% m<>0 =>
  incomplete_step m a b r => r<>b.
proof.
move=> Htwo. rewrite /incomplete_step. move=> [_ [_ [_ [_ [lam [_ Heq]]]]]].
case (r=b); last smt(). move=> Er. move: Heq. rewrite Er /affine_equations.
move=> [Hs [_ Hy]].
have H := mod_difference_zero m _ _ Hs Hy.
have E : (b.`3-a.`3-lam*(b.`2-a.`2))-(-b.`3-a.`3-lam*(b.`2-a.`2))=2*b.`3 by ring.
smt().
qed.

lemma incomplete_inverse_impossible x y m p r : coordinate_laws x y m => p<>idR =>
  !incomplete_step m (group_point x y (-p)) (group_point x y p) r.
proof.
move=> Hc Hp. have Hneg : -p<>idR by smt(op_inv op_id).
have [Hx Hy] : (x (-p)-x p) %% m=0 /\ (y (-p)+y p) %% m=0
  by move: Hc; rewrite /coordinate_laws; smt().
have Htwo : (2*y p) %% m<>0 by move: Hc; rewrite /coordinate_laws; smt().
case (incomplete_step m (group_point x y (-p)) (group_point x y p) r); last smt().
move=> Hstep.
have [lam [_ Heq]] : exists lam, 0 <= lam < m /\
  affine_equations m (x (-p)) (y (-p)) (x p) (y p) r.`2 r.`3 lam
  by move: Hstep; rewrite /incomplete_step /group_point Hp Hneg; smt().
move: Heq. rewrite affine_equationsE. move=> [Hs Hrest].
have Hdx : eqm m (x p-x (-p)) 0 by smt(congr_zero mod0z).
have Hmul := eqmM m lam lam (x p-x (-p)) 0 (eqm_refl m lam) Hdx.
have Hdy : (y p-y (-p)) %% m=0 by smt(mod0z).
have Hsum := mod_add_zero m _ _ Hdy Hy.
have E : (y p-y (-p))+(y (-p)+y p)=2*y p by ring.
smt().
qed.

lemma incomplete_inputs_safe x y m a p r :
  coordinate_laws x y m => a<>idR => p<>idR => a<>p =>
  incomplete_step m (group_point x y a) (group_point x y p) r => add_safe a p.
proof.
move=> Hc Ha Hp Hneq Hstep.
have Hinv := incomplete_inverse_impossible x y m p r Hc Hp.
rewrite /add_safe. smt(notxdiff).
qed.

lemma coordinate_row_exists x y m ca cb p v b :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  2 <= b => row_safe p v b =>
  coordinate_row m b (group_point x y p) (group_point x y v)
    (fun k => group_point x y (table_entry p v k)).
proof.
move=> Hc Hm Hb Hsafe.
have Hi := safe_row_initial_check x y m p v b Hc Hb Hsafe.
have Hp : p<>idR by move: Hsafe; rewrite /row_safe; smt().
have Hv : v<>idR by smt().
rewrite /coordinate_row. split; first exact Hb. split.
+ rewrite /coordinate_safe /group_point Hp Hv /=. smt(congr_zero).
split.
+ simplify. rewrite table_entry0 (negate_point_group x y m ca cb v Hc Hm). trivial.
+ move=> k Hk. simplify.
  have Hstep : add_safe (table_entry p v k) p by move: Hsafe; rewrite /row_safe /add_safe; smt().
  have H := guarded_step_group x y m ca cb (table_entry p v k) p
    (group_point x y (table_entry p v (k+1))) Hc Hm.
  have HE : table_entry p v (k+1)=table_entry p v k +++ p by apply table_entryS.
  have HG : guarded_step m (group_point x y (table_entry p v k)) (group_point x y p)
    (group_point x y (table_entry p v (k+1))) by smt().
  move: HG. rewrite /guarded_step. smt().
qed.

lemma coordinate_row_finite m b p v entries k : coordinate_row m b p v entries =>
  0 <= k < b => !(entries k).`1.
proof.
rewrite /coordinate_row /coordinate_safe. move=> [Hb [[Hp [Hv Hx]] [H0 Hsteps]]] Hk.
case (k=0).
+ move=> ->. rewrite H0 /negate_point Hv /=. trivial.
move=> Hk0. have H := Hsteps (k-1) _; first smt().
move: H. rewrite /incomplete_step. smt().
qed.

lemma coordinate_row_not_base m b (p : coordinate_point) v entries k : (2*p.`3) %% m<>0 =>
  coordinate_row m b p v entries => 0 <= k < b => entries k<>p.
proof.
move=> Htwo. rewrite /coordinate_row /coordinate_safe.
move=> [Hb [[Hp [Hv Hx]] [H0 Hsteps]]] Hk.
case (k=0).
+ move=> ->. rewrite H0 /negate_point Hv /=. smt(congr_zero modz_mod).
move=> Hk0. have H := Hsteps (k-1) _; first smt().
have Hneq := incomplete_output_not_base m (entries (k-1)) p (entries k) Htwo _; smt().
qed.

lemma coordinate_row_entries x y m ca cb p v b entries :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  coordinate_row m b (group_point x y p) (group_point x y v) entries =>
  forall k, 0 <= k < b => entries k=group_point x y (table_entry p v k).
proof.
move=> Hc Hm Hrow.
move: (Hrow). rewrite /coordinate_row. move=> [Hb [Hinitial [H0 Hsteps]]].
have Hp : p<>idR by move: Hinitial; rewrite /coordinate_safe !group_point_flag; smt().
have Htwo : (2*(group_point x y p).`3) %% m<>0
  by rewrite /group_point Hp /=; move: Hc; rewrite /coordinate_laws; smt().
have Hind : forall k, 0 <= k => k<b => entries k=group_point x y (table_entry p v k).
+ apply intind; simplify.
  + move=> Hk. rewrite H0 table_entry0 (negate_point_group x y m ca cb v Hc Hm). trivial.
  + move=> k Hk IH Hkb.
    have Hprev := IH _; first smt().
    have Hstep := Hsteps k _; first smt().
    have Hfinite := coordinate_row_finite m b (group_point x y p) (group_point x y v) entries k Hrow _; first smt().
    have Hneq := coordinate_row_not_base m b (group_point x y p) (group_point x y v) entries k Htwo Hrow _; first smt().
    have Ha : table_entry p v k<>idR by move: Hfinite; rewrite Hprev group_point_flag; smt().
    have Hne : table_entry p v k<>p by smt().
    have HS : incomplete_step m (group_point x y (table_entry p v k)) (group_point x y p) (entries (k+1)) by smt().
    have Hsafe := incomplete_inputs_safe x y m (table_entry p v k) p (entries (k+1)) Hc Ha Hp Hne HS.
    have Hguard : guarded_step m (group_point x y (table_entry p v k)) (group_point x y p) (entries (k+1)).
    + rewrite /guarded_step. split; last exact HS. smt(coordinate_safe_group).
    have Hsound := guarded_step_group x y m ca cb (table_entry p v k) p (entries (k+1)) Hc Hm.
    rewrite table_entryS. smt().
smt().
qed.

lemma coordinate_row_safe x y m ca cb p v b entries :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  coordinate_row m b (group_point x y p) (group_point x y v) entries => row_safe p v b.
proof.
move=> Hc Hm Hrow.
have Hentries := coordinate_row_entries x y m ca cb p v b entries Hc Hm Hrow.
move: (Hrow). rewrite /coordinate_row. move=> [Hb [Hinitial [H0 Hsteps]]].
have Hp : p<>idR by move: Hinitial; rewrite /coordinate_safe !group_point_flag; smt().
have Htwo : (2*(group_point x y p).`3) %% m<>0
  by rewrite /group_point Hp /=; move: Hc; rewrite /coordinate_laws; smt().
rewrite /row_safe. split; first exact Hp. split.
+ move=> k Hk. have H := coordinate_row_finite m b (group_point x y p) (group_point x y v) entries k Hrow Hk.
  move: H. rewrite (Hentries k Hk) group_point_flag. trivial.
+ move=> k Hk.
  have Hk' : 0 <= k < b by smt().
  have Hfinite := coordinate_row_finite m b (group_point x y p) (group_point x y v) entries k Hrow Hk'.
  have Hneq := coordinate_row_not_base m b (group_point x y p) (group_point x y v) entries k Htwo Hrow Hk'.
  have Ha : table_entry p v k<>idR by move: Hfinite; rewrite (Hentries k Hk') group_point_flag; smt().
  have Hne : table_entry p v k<>p by smt().
  have HS := Hsteps k Hk.
  move: HS. rewrite (Hentries k Hk'). move=> HS.
  have Hsafe := incomplete_inputs_safe x y m (table_entry p v k) p (entries (k+1)) Hc Ha Hp Hne HS.
  move: Hsafe. rewrite /add_safe. smt().
qed.

lemma coordinate_tables_exists x y m ca cb P U :
  coordinate_laws x y m => complete_affine_model x y m ca cb => table_safe P U =>
  coordinate_tables m (fun j => group_point x y (P j)) (group_point x y ((2^w-1) *** U))
    (fun j k => group_point x y (perfect_table_pure P U j k)).
proof.
move=> Hc Hm Hsafe. rewrite /coordinate_tables. move=> j Hj. simplify.
have HS : row_safe (P j) ((2^w-1) *** U) (2^w) by move: Hsafe; rewrite /table_safe; smt().
have H := coordinate_row_exists x y m ca cb (P j) ((2^w-1) *** U) (2^w) Hc Hm window_table_width HS.
move: H. by rewrite /table_entry /perfect_table_pure.
qed.

lemma coordinate_tables_sound x y m ca cb P U table :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  coordinate_tables m (fun j => group_point x y (P j)) (group_point x y ((2^w-1) *** U)) table =>
  table_safe P U /\ forall j k, 0 <= j < l => 0 <= k < 2^w =>
    table j k=group_point x y (perfect_table_pure P U j k).
proof.
move=> Hc Hm. rewrite /coordinate_tables. move=> Hrows. split.
+ rewrite /table_safe. move=> j Hj.
  have H := Hrows j Hj. move: H. simplify. move=> H.
  exact (coordinate_row_safe x y m ca cb (P j) ((2^w-1) *** U) (2^w) (table j) Hc Hm H).
+ move=> j k Hj Hk. have H := Hrows j Hj.
  have HE := coordinate_row_entries x y m ca cb (P j) ((2^w-1) *** U) (2^w) (table j) Hc Hm H k Hk.
  move: HE. by rewrite /table_entry /perfect_table_pure.
qed.
