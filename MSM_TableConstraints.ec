require import AllCore Int IntDiv StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract MSM_TableConstruction MSM_WithTable.

(* Figure 2's three coordinate equations, with the output identity bit zero.
   x and y are integer representatives of foreign-field coordinates modulo m.
   No unequal-x guard is included in this relation. *)
op slope_constraint (x y : R -> int) m a p lam =
  (y p - y a - lam * (x p - x a)) %% m = 0.

op incomplete_constraints (x y : R -> int) m a p r lam =
  r <> idR /\ slope_constraint x y m a p lam /\
  (x a + x p + x r - lam * lam) %% m = 0 /\
  (-y r - y a - lam * (x r - x a)) %% m = 0.

(* Explicit coordinate-interface obligations, not new global axioms.
   These are the usual nonidentity/no-2-torsion, negation and x-coordinate
   properties of the intended odd-characteristic curve subgroup. *)
op coordinate_laws (x y : R -> int) m =
  1 < m /\
  (forall p, p <> idR => (2 * y p) %% m <> 0) /\
  (forall p, p <> idR =>
    (x (-p) - x p) %% m = 0 /\ (y (-p) + y p) %% m = 0) /\
  (forall a p, a <> idR => p <> idR =>
    (xdiff a p <=> (x p - x a) %% m <> 0)).

(* The same safe-input correctness obligation as the abstract addition
   interface, now stated for witnessed coordinate equations. This does not
   assume anything about exceptional-input rejection or table safety. *)
op safe_constraint_correct (x y : R -> int) m =
  forall a p r lam, add_safe a p =>
    incomplete_constraints x y m a p r lam => r = a +++ p.

lemma mod_sub_zero a b m : a %% m = 0 => b %% m = 0 =>
  (a-b) %% m = 0.
proof. move=> Ha Hb. rewrite -modzBm Ha Hb. smt(mod0z). qed.

lemma mod_mul_zero a b m : a %% m = 0 => (b*a) %% m = 0.
proof. move=> Ha. rewrite -modzMmr Ha. smt(mod0z). qed.

(* A successful addition of p cannot return p: the two slope equations
   would imply 2*y(p)=0, independently of the lambda-squared equation. *)
lemma constraints_output_not_base x y m a p r lam :
  (2 * y p) %% m <> 0 =>
  incomplete_constraints x y m a p r lam => r <> p.
proof.
rewrite /incomplete_constraints /slope_constraint.
move=> Hnonzero [Hr [Hs [Hsq Hout]]].
case (r=p)=> Heq; last smt(). subst r.
have H := mod_sub_zero _ _ m Hs Hout.
have E : (y p - y a - lam * (x p - x a)) -
  (-y p - y a - lam * (x p - x a)) = 2 * y p by ring.
smt().
qed.

(* The input -p is rejected by the first slope equation itself. *)
lemma constraints_inverse_impossible x y m p r lam :
  coordinate_laws x y m => p <> idR =>
  ! incomplete_constraints x y m (-p) p r lam.
proof.
rewrite /coordinate_laws /incomplete_constraints /slope_constraint.
move=> [Hm [Htwo [Hneg Hx]]] Hp.
case (incomplete_constraints x y m (-p) p r lam); last smt().
rewrite /incomplete_constraints /slope_constraint.
move=> [Hr [Hs [Hsq Hout]]].
have [Hxneg Hyneg] := Hneg p Hp.
have Hdelta : (x p - x (-p)) %% m = 0.
+ have H := mod_sub_zero 0 _ m (mod0z m) Hxneg.
  have E : 0 - (x (-p) - x p) = x p - x (-p) by ring.
  smt().
have Hy : (y p - y (-p)) %% m = 0.
+ have H' := mod_sub_zero _ _ m Hs (mod_mul_zero _ (-lam) m Hdelta).
  have E : (y p-y (-p)-lam*(x p-x (-p))) -
    (-lam*(x p-x (-p))) = y p-y (-p) by ring.
  smt().
have Hsum : (2*y p) %% m = 0.
+ rewrite -(_ : (y p-y (-p)) + (y (-p)+y p) = 2*y p) 1:/#.
  rewrite -modzDm Hy Hyneg. smt(mod0z).
smt().
qed.

(* Only the initial unequal-x test is present. Every later step consists
   solely of the existing Figure 2 constraints. *)
op accepted_table_row (x y : R -> int) m p v b
    (entries : int -> R) (slopes : int -> int) =
  0 < b /\ p <> idR /\ v <> idR /\
  (x p - x v) %% m <> 0 /\
  entries 0 = -v /\
  forall k, 0 <= k < b-1 =>
    incomplete_constraints x y m (entries k) p (entries (k+1)) (slopes k).

lemma accepted_entry_nonzero x y m p v b entries slopes k :
  accepted_table_row x y m p v b entries slopes =>
  0 <= k < b => entries k <> idR.
proof.
rewrite /accepted_table_row.
move=> [Hb [Hp [Hv [Hx [Hinit Hsteps]]]]] Hk.
case (k=0); first smt(op_inv op_id).
move=> Hk0. have H := Hsteps (k-1) _; first smt().
move: H. rewrite /incomplete_constraints. smt().
qed.

lemma accepted_entry_not_base x y m p v b entries slopes k :
  coordinate_laws x y m =>
  accepted_table_row x y m p v b entries slopes =>
  0 <= k < b => entries k <> p.
proof.
move=> Hcoord Hrow Hk.
move: (Hrow). rewrite /accepted_table_row.
move=> [Hb [Hp [Hv [Hx [Hinit Hsteps]]]]].
have Hneg : (x (-v)-x v) %% m = 0
  by move: Hcoord; rewrite /coordinate_laws; smt().
case (k=0); first smt().
move=> Hk0.
have Hstep := Hsteps (k-1) _; first smt().
have Htwo : (2*y p) %% m <> 0 by move: Hcoord; rewrite /coordinate_laws; smt().
have H := constraints_output_not_base x y m _ _ _ _ Htwo Hstep.
smt().
qed.

lemma accepted_step_safe x y m p v b entries slopes k :
  coordinate_laws x y m =>
  accepted_table_row x y m p v b entries slopes =>
  0 <= k < b-1 => add_safe (entries k) p.
proof.
move=> Hcoord Hrow Hk.
have Hnz := accepted_entry_nonzero x y m p v b entries slopes k Hrow _; first smt().
have Hneq := accepted_entry_not_base x y m p v b entries slopes k Hcoord Hrow _; first smt().
move: (Hrow). rewrite /accepted_table_row.
move=> [Hb [Hp [Hv [Hx [Hinit Hsteps]]]]].
have Hstep := Hsteps k Hk.
have Hnotneg := constraints_inverse_impossible x y m p (entries (k+1)) (slopes k) Hcoord Hp.
rewrite /add_safe. smt(notxdiff).
qed.

lemma accepted_table_entries x y m p v b entries slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  accepted_table_row x y m p v b entries slopes =>
  forall k, 0 <= k < b => entries k = table_entry p v k.
proof.
move=> Hcoord Hcorrect Hrow.
have Hinit : entries 0 = -v by move: Hrow; rewrite /accepted_table_row; smt().
have Hsteps : forall k, 0 <= k < b-1 =>
  incomplete_constraints x y m (entries k) p (entries (k+1)) (slopes k)
  by move: Hrow; rewrite /accepted_table_row; smt().
have Hind : forall k, 0 <= k => k < b => entries k = table_entry p v k.
+ apply intind.
  + move=> Hrange. by rewrite Hinit table_entry0.
  + move=> k Hk IH Hrange.
  have Hrange' : 0 <= k < b by smt().
  have Hsafe := accepted_step_safe x y m p v b entries slopes k Hcoord Hrow _; first smt().
  have Hstep := Hsteps k _; first smt().
  have Hsum : entries (k+1) = entries k +++ p by move: Hcorrect; rewrite /safe_constraint_correct; smt().
  by rewrite Hsum (IH _) 1:/# table_entryS.
move=> k [Hk Hb]. exact (Hind k Hk Hb).
qed.

(* Thus the guards in TableBuilder are redundant for accepting witnesses.
   This is soundness, not a claim that every initial offset is admissible. *)
lemma accepted_table_row_safe x y m p v b entries slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  accepted_table_row x y m p v b entries slopes => row_safe p v b.
proof.
move=> Hcoord Hcorrect Hrow.
have Hentries := accepted_table_entries x y m p v b entries slopes Hcoord Hcorrect Hrow.
have Hnz := accepted_entry_nonzero x y m p v b entries slopes.
have Hsafe := accepted_step_safe x y m p v b entries slopes.
rewrite /row_safe.
have Hp : p <> idR by move: Hrow; rewrite /accepted_table_row; smt().
split; first exact Hp.
split.
+ move=> k Hk. rewrite -(Hentries k Hk). exact (Hnz k Hrow Hk).
+ move=> k Hk. have Hk' : 0 <= k < b by smt().
  rewrite -(Hentries k Hk'). have H := Hsafe k Hcoord Hrow Hk.
  move: H. rewrite /add_safe. smt().
qed.

lemma accepted_table_builder_succeeds x y m p v b entries slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  accepted_table_row x y m p v b entries slopes =>
  phoare [TableBuilder.row : arg = (p,v,b) ==>
    res.`1 /\ forall k, 0 <= k < b => res.`2 k = entries k] = 1%r.
proof.
move=> Hcoord Hcorrect Hrow.
have Hsafe := accepted_table_row_safe x y m p v b entries slopes Hcoord Hcorrect Hrow.
have Hentries := accepted_table_entries x y m p v b entries slopes Hcoord Hcorrect Hrow.
have Hb : 0 < b by move: Hrow; rewrite /accepted_table_row; smt().
conseq (table_row_spec p v b Hb); smt().
qed.

(* The implied guard is also the actual modular coordinate inequality. *)
lemma accepted_step_distinct_x x y m p v b entries slopes k :
  coordinate_laws x y m =>
  accepted_table_row x y m p v b entries slopes =>
  0 <= k < b-1 => (x p - x (entries k)) %% m <> 0.
proof.
move=> Hcoord Hrow Hk.
have Hsafe := accepted_step_safe x y m p v b entries slopes k Hcoord Hrow Hk.
move: Hsafe Hcoord. rewrite /add_safe /coordinate_laws. smt().
qed.

op accepted_tables (x y : R -> int) m P U table slopes =
  forall j, 0 <= j < l =>
    accepted_table_row x y m (P j) ((2^w-1) *** U) (2^w) (table j) (slopes j).

lemma accepted_tables_safe x y m P U table slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  accepted_tables x y m P U table slopes => table_safe P U.
proof.
rewrite /accepted_tables /table_safe.
move=> Hcoord Hcorrect Hrows j Hj.
exact (accepted_table_row_safe x y m (P j) ((2^w-1) *** U) (2^w)
  (table j) (slopes j) Hcoord Hcorrect (Hrows j Hj)).
qed.

lemma accepted_tables_match x y m P U table slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  accepted_tables x y m P U table slopes => table_matches table P U.
proof.
rewrite /accepted_tables /table_matches.
move=> Hcoord Hcorrect Hrows j k Hj Hk.
have H := accepted_table_entries x y m (P j) ((2^w-1) *** U) (2^w)
  (table j) (slopes j) Hcoord Hcorrect (Hrows j Hj) k Hk.
move: H. rewrite /table_entry /perfect_table_pure. smt().
qed.

(* The MSM consumes witnessed table entries directly, without executing the
   guarded builder. All table guards follow from the accepted constraints. *)
lemma constraint_table_msm_soundness x y m P s U table slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  accepted_tables x y m P U table slopes => valid_windows s =>
  phoare [ConstructedMSM.with_table : arg = (P,s,U,table) ==>
    res.`1 => res.`2 = multiScalarMul_Simpl s P T l] = 1%r.
proof.
move=> Hcoord Hcorrect Hrows Hwindows.
have Hsafe := accepted_tables_safe x y m P U table slopes Hcoord Hcorrect Hrows.
have Hmatch := accepted_tables_match x y m P U table slopes Hcoord Hcorrect Hrows.
conseq (with_table_soundness P s U table); smt().
qed.
