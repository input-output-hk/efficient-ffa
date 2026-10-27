import EfficientFFA.EllipticCurve.Complete

namespace EfficientFFA.MSM

/-- The mathematical entry in the offset table: i*base - offset. -/
def entry {G : Type*} [AddCommGroup G] (base offset : G) (i : ℕ) : G := i • base - offset

theorem entry_succ {G : Type*} [AddCommGroup G] (base offset : G) (i : ℕ) :
    entry base offset (i+1) = entry base offset i + base := by
  simp only [entry, succ_nsmul]
  abel

/-- Every represented entry is finite; each addition avoids equal/opposite operands. -/
def TableSafe {G : Type*} [AddCommGroup G] (base offset : G) (steps : ℕ) : Prop :=
  (∀ i, i ≤ steps → entry base offset i ≠ 0) ∧
  (∀ i, i < steps → entry base offset i ≠ base ∧ entry base offset i ≠ -base)

/-- Raw affine equations only: no per-step x-inequality or curve-membership checks. -/
def TableChecks {K : Type*} [Field K] (base : EllipticCurve.Coordinates K)
    (table : ℕ → EllipticCurve.Coordinates K) (steps : ℕ) : Prop :=
  ∀ i, i < steps → ∃ slope, EllipticCurve.AddChecks (table i) base (table (i+1)) slope

end EfficientFFA.MSM

namespace EfficientFFA.EllipticCurve

/-- With distinct coordinate pairs, the accepted slope equation forces distinct x-coordinates. -/
theorem x_ne_of_add_checks {K : Type*} [Field K] {P Q R : Coordinates K} {slope : K}
    (hne : P ≠ Q) (hc : AddChecks P Q R slope) : P.x ≠ Q.x := by
  intro hx
  have hy : P.y = Q.y := by
    have h := hc.slope_eq
    rw [← hx, sub_self, mul_zero, sub_zero] at h
    exact (sub_eq_zero.mp h).symm
  apply hne
  cases P; cases Q
  simp_all

namespace Curve
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

omit [DecidableEq K] in
/-- Finite affine points share x exactly when they are equal or opposite in the group. -/
theorem same_x_iff {P Q : Coordinates K} (hP : C.OnCurve P) (hQ : C.OnCurve Q) :
    P.x = Q.x ↔ C.point P hP = C.point Q hQ ∨ C.point P hP = -C.point Q hQ :=
  WeierstrassCurve.Affine.Point.X_eq_iff

/-- A valid repeated-base step cannot output the base: that would make its input zero. -/
theorem repeated_step {A base R : Coordinates K} {slope : K}
    (hA : C.OnCurve A) (hbase : C.OnCurve base) (hne : A ≠ base)
    (hc : AddChecks A base R slope) :
    A.x ≠ base.x ∧ ∃ hR : C.OnCurve R,
      C.point R hR = C.point A hA + C.point base hbase ∧ R ≠ base := by
  have hx := x_ne_of_add_checks hne hc
  obtain ⟨hR, he⟩ := C.addition_sound hA hbase hx hc
  refine ⟨hx, hR, he, ?_⟩
  intro hr
  apply C.point_ne_zero hA
  apply add_right_cancel (b := C.point base hbase)
  calc
    C.point A hA + C.point base hbase = C.point R hR := he.symm
    _ = C.point base hbase := by subst R; rfl
    _ = 0 + C.point base hbase := (zero_add _).symm

/-- All accepted table entries are valid and have the stated group meaning.
Only the initial x-guard is assumed; every later guard is derived from the
raw equations and the repeated-base invariant. No torsion assumption is used. -/
theorem table_sound {base : Coordinates K} {table : ℕ → Coordinates K} {steps : ℕ}
    (hbase : C.OnCurve base) (hstart : C.OnCurve (table 0))
    (hfirst : (table 0).x ≠ base.x) (hc : MSM.TableChecks base table steps) :
    ∀ i, i ≤ steps → ∃ hi : C.OnCurve (table i),
      C.point (table i) hi = i • C.point base hbase + C.point (table 0) hstart ∧ table i ≠ base := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨hstart, by simp, ?_⟩
    intro h
    exact hfirst (congrArg Coordinates.x h)
  | succ i ih =>
    intro hle
    obtain ⟨hi, he, hne⟩ := ih (by omega)
    obtain ⟨slope, hstep⟩ := hc i (by omega)
    obtain ⟨_, hn, hg, hne'⟩ := C.repeated_step hi hbase hne hstep
    refine ⟨hn, ?_, hne'⟩
    rw [hg, he, succ_nsmul]
    abel

theorem table_guards {base : Coordinates K} {table : ℕ → Coordinates K} {steps : ℕ}
    (hbase : C.OnCurve base) (hstart : C.OnCurve (table 0))
    (hfirst : (table 0).x ≠ base.x) (hc : MSM.TableChecks base table steps) :
    ∀ i, i < steps → (table i).x ≠ base.x := by
  intro i hi
  obtain ⟨_, _, hne⟩ := C.table_sound hbase hstart hfirst hc i (by omega)
  obtain ⟨slope, hs⟩ := hc i hi
  exact x_ne_of_add_checks hne hs

/-- Extract coordinates from a group point; zero's dummy coordinates are never
used as an affine point without a separate nonzero proof. -/
def coordinates (g : C.Point) : Coordinates K :=
  match g with
  | .zero => ⟨0, 0⟩
  | .some x y _ => ⟨x, y⟩

omit [DecidableEq K] in
theorem coordinates_on_curve {g : C.Point} (hg : g ≠ 0) : C.OnCurve (C.coordinates g) := by
  cases g with
  | zero => exact False.elim (hg rfl)
  | some x y h => exact (C.equation_iff _).mp h.1

omit [DecidableEq K] in
theorem point_coordinates {g : C.Point} (hg : g ≠ 0) :
    C.point (C.coordinates g) (C.coordinates_on_curve hg) = g := by
  cases g with
  | zero => exact False.elim (hg rfl)
  | some x y h => rfl

/-- Accepted tables exclude all the exceptional group entries, including the final zero. -/
theorem table_safe {base : Coordinates K} {table : ℕ → Coordinates K} {steps : ℕ}
    {offset : C.Point} (hbase : C.OnCurve base) (hstart : C.OnCurve (table 0))
    (hzero : C.point (table 0) hstart = -offset)
    (hfirst : (table 0).x ≠ base.x) (hc : MSM.TableChecks base table steps) :
    MSM.TableSafe (C.point base hbase) offset steps := by
  have hmeaning : ∀ i, i ≤ steps → ∃ hi : C.OnCurve (table i),
      C.point (table i) hi = MSM.entry (C.point base hbase) offset i := by
    intro i hi
    obtain ⟨h, he, _⟩ := C.table_sound hbase hstart hfirst hc i hi
    exact ⟨h, by simpa only [hzero, MSM.entry, sub_eq_add_neg] using he⟩
  constructor
  · intro i hi
    obtain ⟨h, he⟩ := hmeaning i hi
    rw [← he]
    exact C.point_ne_zero h
  · intro i hi
    obtain ⟨h, he⟩ := hmeaning i (by omega)
    have hx := C.table_guards hbase hstart hfirst hc i hi
    rw [← he]
    exact ⟨fun hh => hx ((C.same_x_iff h hbase).mpr (Or.inl hh)),
      fun hh => hx ((C.same_x_iff h hbase).mpr (Or.inr hh))⟩

/-- Safe mathematical entries supply actual affine slope and coordinate witnesses. -/
theorem table_complete {base start : Coordinates K} {offset : C.Point} {steps : ℕ}
    (hbase : C.OnCurve base) (hstart : C.OnCurve start)
    (hzero : C.point start hstart = -offset)
    (hsafe : MSM.TableSafe (C.point base hbase) offset steps) :
    ∃ table : ℕ → Coordinates K, table 0 = start ∧ MSM.TableChecks base table steps := by
  let table : ℕ → Coordinates K := fun i => C.coordinates (MSM.entry (C.point base hbase) offset i)
  have hv : ∀ i, i ≤ steps → C.OnCurve (table i) :=
    fun i hi => C.coordinates_on_curve (hsafe.1 i hi)
  have he : ∀ i, ∀ hi : i ≤ steps,
      C.point (table i) (hv i hi) = MSM.entry (C.point base hbase) offset i :=
    fun i hi => C.point_coordinates (hsafe.1 i hi)
  refine ⟨table, ?_, ?_⟩
  · apply C.point_injective (hP := hv 0 (by omega)) (hQ := hstart)
    rw [he 0 (Nat.zero_le _), hzero]
    simp [MSM.entry]
  · intro i hi
    have hx : (table i).x ≠ base.x := by
      intro hh
      have hg := (C.same_x_iff (hv i (by omega)) hbase).mp hh
      rw [he i (Nat.le_of_lt hi)] at hg
      exact hg.elim (hsafe.2 i hi).1 (hsafe.2 i hi).2
    obtain ⟨R, slope, hc, hR, hg⟩ := C.addition_complete (hv i (by omega)) hbase hx
    have hRnext : R = table (i+1) := by
      apply C.point_injective (hP := hR) (hQ := hv (i+1) (by omega))
      rw [hg, he i (by omega), he (i+1) (by omega), MSM.entry_succ]
    exact ⟨slope, by simpa only [hRnext] using hc⟩

/-- Exact witness-existence criterion, with the paper's initial x-guard explicit. -/
theorem table_witnesses_iff {base start : Coordinates K} {offset : C.Point} {steps : ℕ}
    (hbase : C.OnCurve base) (hstart : C.OnCurve start)
    (hzero : C.point start hstart = -offset) (hfirst : start.x ≠ base.x) :
    (∃ table : ℕ → Coordinates K, table 0 = start ∧ MSM.TableChecks base table steps) ↔
      MSM.TableSafe (C.point base hbase) offset steps := by
  constructor
  · rintro ⟨table, ht, hc⟩
    have hv : C.OnCurve (table 0) := by simpa only [ht] using hstart
    apply C.table_safe hbase hv (table := table)
    · simpa only [ht] using hzero
    · simpa only [ht] using hfirst
    · exact hc
  · exact C.table_complete hbase hstart hzero

/-- A range-bounded lookup selects a valid point with the required offset value. -/
theorem table_lookup_sound {base : Coordinates K} {table : ℕ → Coordinates K}
    {steps : ℕ} {offset : C.Point}
    (hbase : C.OnCurve base) (hstart : C.OnCurve (table 0))
    (hzero : C.point (table 0) hstart = -offset)
    (hfirst : (table 0).x ≠ base.x) (hc : MSM.TableChecks base table steps)
    (index : Fin (steps+1)) :
    ∃ hi : C.OnCurve (table index.val),
      C.point (table index.val) hi = MSM.entry (C.point base hbase) offset index.val := by
  obtain ⟨hi, he, _⟩ := C.table_sound hbase hstart hfirst hc index.val (by omega)
  exact ⟨hi, by simpa only [hzero, MSM.entry, sub_eq_add_neg] using he⟩

/-- Affine coordinates of the group inverse on the short Weierstrass model. -/
def opposite (P : Coordinates K) : Coordinates K := ⟨P.x, -P.y⟩

omit [DecidableEq K] in
theorem opposite_on_curve {P : Coordinates K} (hP : C.OnCurve P) : C.OnCurve (opposite P) := by
  simpa only [OnCurve, opposite, neg_sq] using hP

omit [DecidableEq K] in
theorem point_opposite {P : Coordinates K} (hP : C.OnCurve P) :
    C.point (opposite P) (C.opposite_on_curve hP) = -C.point P hP := by
  simp only [point, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq]
  simp [opposite, W, model, WeierstrassCurve.Affine.negY]

/-- The paper's initial x(P) != x(V) guard, stated with an actual finite V. -/
theorem offset_table_witnesses_iff {base V : Coordinates K} {steps : ℕ}
    (hbase : C.OnCurve base) (hV : C.OnCurve V) (hguard : base.x ≠ V.x) :
    (∃ table : ℕ → Coordinates K, table 0 = opposite V ∧ MSM.TableChecks base table steps) ↔
      MSM.TableSafe (C.point base hbase) (C.point V hV) steps :=
  C.table_witnesses_iff hbase (C.opposite_on_curve hV) (C.point_opposite hV) hguard.symm

end Curve
end EfficientFFA.EllipticCurve
