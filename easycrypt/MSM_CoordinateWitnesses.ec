require import AllCore Int IntDiv StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
  MultiScalarMul_Abstract_Completeness MSM_TableConstruction MSM_WithTable.
require import AffineAddition MSM_TableConstraints MSM_RejectionBound MSM_WindowOrder.
import Ring.IntID IntOrder.

(* Representation obligations for the already abstract group. The last
   clause specifies its addition via the standard affine formulas. No
   constraint soundness or witness-existence property is assumed here. *)
op affine_group_model (x y : R -> int) m =
  prime m /\
  (forall a b, a <> idR => b <> idR =>
    eqm m (x a) (x b) => eqm m (y a) (y b) => a=b) /\
  (forall a b, add_safe a b =>
    let sl = affine_slope m (x a) (y a) (x b) (y b) in
    let sx = affine_x (x a) (x b) sl in
    eqm m (x (a +++ b)) sx /\
    eqm m (y (a +++ b)) (affine_y (x a) (y a) sx sl)).

op coordinate_slope (x y : R -> int) m a b =
  affine_slope m (x a) (y a) (x b) (y b).

lemma incomplete_equationsE x y m a b r lam :
  incomplete_constraints x y m a b r lam <=>
  r <> idR /\ affine_equations m (x a) (y a) (x b) (y b) (x r) (y r) lam.
proof. rewrite /incomplete_constraints /slope_constraint /affine_equations. smt(). qed.

lemma safe_coordinate_denominator x y m a b :
  coordinate_laws x y m => add_safe a b => (x b-x a) %% m <> 0.
proof. rewrite /coordinate_laws /add_safe. smt(). qed.

lemma safe_sum_nonzero x y m a b :
  coordinate_laws x y m => add_safe a b => a +++ b <> idR.
proof.
move=> Hcoord Hsafe.
have Hden := safe_coordinate_denominator x y m a b Hcoord Hsafe.
have Hb : b <> idR by move: Hsafe; rewrite /add_safe; smt().
have Hneg : (x (-b)-x b) %% m = 0
  by move: Hcoord; rewrite /coordinate_laws; smt().
case (a +++ b = idR); last smt().
move=> Hzero. have Heq : a = -b by smt(op_eq_neg).
have Hx : eqm m (x (-b)) (x b) by smt(congr_zero).
smt(congr_zero).
qed.

lemma safe_constraint_correct_from_model x y m :
  coordinate_laws x y m => affine_group_model x y m => safe_constraint_correct x y m.
proof.
move=> Hcoord. rewrite /affine_group_model.
move=> [Hprime [Hinj Hlaw]]. rewrite /safe_constraint_correct.
move=> a b r lam Hsafe. rewrite incomplete_equationsE. move=> [Hr Heq].
have Hnz := safe_coordinate_denominator x y m a b Hcoord Hsafe.
have Huniq := affine_equations_unique m (x a) (y a) (x b) (y b) (x r) (y r) lam Hprime Hnz Heq.
have Hsum := Hlaw a b Hsafe.
have Hnonzero := safe_sum_nonzero x y m a b Hcoord Hsafe.
apply (Hinj r (a +++ b)); smt().
qed.

lemma safe_constraint_witness x y m a b :
  coordinate_laws x y m => affine_group_model x y m => add_safe a b =>
  incomplete_constraints x y m a b (a +++ b) (coordinate_slope x y m a b).
proof.
move=> Hcoord. rewrite /affine_group_model.
move=> [Hprime [Hinj Hlaw]] Hsafe.
have Hnz := safe_coordinate_denominator x y m a b Hcoord Hsafe.
have Hs := affine_slope_valid m (x a) (y a) (x b) (y b) Hprime Hnz.
have Hsum := Hlaw a b Hsafe. move: Hsum. simplify. move=> [Hx Hy].
have Hnonzero := safe_sum_nonzero x y m a b Hcoord Hsafe.
rewrite incomplete_equationsE affine_equationsE /coordinate_slope.
have Hyy := affine_y_congr m (x a) (y a) (x (a +++ b))
  (affine_x (x a) (x b) (affine_slope m (x a) (y a) (x b) (y b)))
  (affine_slope m (x a) (y a) (x b) (y b))
  (affine_slope m (x a) (y a) (x b) (y b)) Hx
  (eqm_refl m (affine_slope m (x a) (y a) (x b) (y b))).
smt().
qed.

op row_slopes x y m p v = fun k => coordinate_slope x y m (table_entry p v k) p %% m.

lemma safe_row_initial_check x y m p v b :
  coordinate_laws x y m => 2 <= b => row_safe p v b =>
  v <> idR /\ (x p-x v) %% m <> 0.
proof.
move=> Hcoord Hb. rewrite /row_safe. move=> [Hp [Hnz Hdiff]].
have Hzero : table_entry p v 0 = -v by apply table_entry0.
have Hv : v <> idR by smt(op_inv op_id').
have Hstep : xdiff (-v) p by smt().
have Hden : (x p-x (-v)) %% m <> 0.
+ apply (safe_coordinate_denominator x y m (-v) p Hcoord).
  rewrite /add_safe. smt().
have Hneg : (x (-v)-x v) %% m = 0
  by move: Hcoord; rewrite /coordinate_laws; smt().
have Heq : eqm m (x (-v)) (x v) by smt(congr_zero).
have Hdx := eqmB m (x p) (x p) (x (-v)) (x v) (eqm_refl m (x p)) Heq.
smt().
qed.

lemma safe_row_has_witnesses x y m p v b :
  coordinate_laws x y m => affine_group_model x y m =>
  2 <= b => row_safe p v b =>
  accepted_table_row x y m p v b (table_entry p v) (row_slopes x y m p v).
proof.
move=> Hcoord Hmodel Hb Hsafe.
have Hinitial := safe_row_initial_check x y m p v b Hcoord Hb Hsafe.
move: (Hsafe). rewrite /row_safe. move=> [Hp [Hnz Hdiff]].
rewrite /accepted_table_row. split; first smt().
split; first exact Hp. split; first smt(). split; first smt().
split; first exact (table_entry0 p v).
move=> k Hk.
have Hstep : add_safe (table_entry p v k) p by rewrite /add_safe; smt().
have H := safe_constraint_witness x y m (table_entry p v k) p Hcoord Hmodel Hstep.
rewrite /row_slopes table_entryS incomplete_equationsE.
move: H. rewrite incomplete_equationsE. move=> [Hnonzero Heq].
split; first exact Hnonzero. exact (affine_equations_slope_residue m _ _ _ _ _ _ _ Heq).
qed.

lemma table_row_constraints_iff_safe x y m p v b :
  coordinate_laws x y m => affine_group_model x y m => 2 <= b =>
  ((exists entries slopes, accepted_table_row x y m p v b entries slopes)
    <=> row_safe p v b).
proof.
move=> Hcoord Hmodel Hb. split.
+ move=> [entries slopes Hrow].
  exact (accepted_table_row_safe x y m p v b entries slopes Hcoord
    (safe_constraint_correct_from_model x y m Hcoord Hmodel) Hrow).
+ move=> Hsafe. exists (table_entry p v) (row_slopes x y m p v).
  exact (safe_row_has_witnesses x y m p v b Hcoord Hmodel Hb Hsafe).
qed.

lemma window_table_width : 2 <= 2^w.
proof.
have Hw : 0 < w by smt(param_pos).
have Hpow : 0 < 2^(w-1) by smt(expr_gt0).
have Heq : 2^w = 2*2^(w-1) by rewrite expr_pred; smt().
smt().
qed.

op table_slopes x y m (P : int -> R) U = fun j =>
  row_slopes x y m (P j) ((2^w-1) *** U).

lemma safe_table_has_witnesses x y m P U :
  coordinate_laws x y m => affine_group_model x y m => table_safe P U =>
  accepted_tables x y m P U (perfect_table_pure P U) (table_slopes x y m P U).
proof.
move=> Hcoord Hmodel. rewrite /table_safe. move=> Hsafe.
rewrite /accepted_tables /table_slopes. move=> j Hj.
have H := safe_row_has_witnesses x y m (P j) ((2^w-1) *** U) (2^w)
  Hcoord Hmodel window_table_width (Hsafe j Hj).
move: H. rewrite /table_entry /perfect_table_pure. smt().
qed.

lemma table_constraints_iff_safe x y m P U :
  coordinate_laws x y m => affine_group_model x y m =>
  ((exists table slopes, accepted_tables x y m P U table slopes) <=> table_safe P U).
proof.
move=> Hcoord Hmodel. split.
+ move=> [table slopes Haccepted].
  exact (accepted_tables_safe x y m P U table slopes Hcoord
    (safe_constraint_correct_from_model x y m Hcoord Hmodel) Haccepted).
+ move=> Hsafe. exists (perfect_table_pure P U) (table_slopes x y m P U).
  exact (safe_table_has_witnesses x y m P U Hcoord Hmodel Hsafe).
qed.

(* The probability is now about existence of satisfying coordinate-table
   witnesses, not merely success of the abstract guarded row builder. *)
lemma table_witness_failure_bound x y m P :
  coordinate_laws x y m => affine_group_model x y m =>
  nonzero_bases P => scalar_invertible (2^w-1) =>
  mu r_distr (fun u => ! (exists table slopes, accepted_tables x y m P u table slopes))
  <= (l*(2^w+1))%r / group_cardinality%r.
proof.
move=> Hcoord Hmodel HP Hinv.
have Heq : (fun u => ! (exists table slopes, accepted_tables x y m P u table slopes)) =
  (fun u => ! table_safe P u)
  by apply fun_ext=> u; smt(table_constraints_iff_safe).
rewrite Heq.
have H := table_rejection_bound P HP Hinv.
move: H. rewrite point_mass_cardinality. smt(Real.fromintM).
qed.

(* Only the table component is expressed by coordinate constraints here;
   doubling, offset calculation and the MSM loop retain their abstract
   semantics. This is not a full coordinate-circuit completeness theorem. *)
op table_witness_pipeline_accepts x y m P s u =
  (exists table slopes, accepted_tables x y m P u table slopes) /\
  valid_windows s /\ l *** u <> idR /\ loop_ok P s u.

lemma table_witness_pipeline_equiv x y m P s u :
  coordinate_laws x y m => affine_group_model x y m =>
  table_witness_pipeline_accepts x y m P s u = construction_accepts P s u.
proof.
move=> Hcoord Hmodel.
rewrite /table_witness_pipeline_accepts /construction_accepts.
smt(table_constraints_iff_safe).
qed.

lemma little_endian_table_witness_failure_bound x y m P s :
  coordinate_laws x y m => affine_group_model x y m =>
  nonzero_bases P => valid_windows s =>
  scalar_invertible (2^w-1) => scalar_invertible l =>
  mu r_distr (fun u => !table_witness_pipeline_accepts x y m P (reverse_windows T s) u)
  <= (1+l*(2^w+1)+2*T*l)%r / group_cardinality%r.
proof.
move=> Hcoord Hmodel HP Hs Htable Hinitial.
have Heq : (fun u => !table_witness_pipeline_accepts x y m P (reverse_windows T s) u) =
  (fun u => !construction_accepts P (reverse_windows T s) u)
  by apply fun_ext=> u; smt(table_witness_pipeline_equiv).
rewrite Heq.
have Hvalid : valid_windows (reverse_windows T s) by smt(reverse_windows_valid).
have H := construction_failure_mass P (reverse_windows T s) HP Hvalid Htable Hinitial.
move: H. rewrite /rejection_bound point_mass_cardinality. smt().
qed.

lemma modeled_little_endian_table_soundness x y m P s U table slopes :
  coordinate_laws x y m => affine_group_model x y m =>
  accepted_tables x y m P U table slopes => valid_windows s =>
  phoare [LittleEndianMSM.with_table : arg=(P,s,U,table) ==>
    res.`1 => res.`2 = msm_little_endian s P T l] = 1%r.
proof.
move=> Hcoord Hmodel Htable Hwindows.
exact (little_endian_constraint_table_soundness x y m P s U table slopes Hcoord
  (safe_constraint_correct_from_model x y m Hcoord Hmodel) Htable Hwindows).
qed.

lemma table_slopes_bounded x y m P U j k : affine_group_model x y m =>
  0 <= table_slopes x y m P U j k < m.
proof.
rewrite /affine_group_model /table_slopes /row_slopes.
smt(modz_ge0 ltz_pmod gt0_prime).
qed.
