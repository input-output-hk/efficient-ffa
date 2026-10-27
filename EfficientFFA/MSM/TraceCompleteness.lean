import EfficientFFA.MSM.Trace

namespace EfficientFFA.EllipticCurve.Curve
open MSM
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

/-- Canonical coordinates supply the incomplete-add equations for safe operands. -/
theorem coordinates_add_witnesses {a b : C.Point} (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : a ≠ b) (hneg : a ≠ -b) :
    (C.coordinates a).x ≠ (C.coordinates b).x ∧
    ∃ slope, AddChecks (C.coordinates a) (C.coordinates b) (C.coordinates (a+b)) slope := by
  have hxa := C.coordinates_on_curve ha
  have hxb := C.coordinates_on_curve hb
  have hx : (C.coordinates a).x ≠ (C.coordinates b).x := by
    intro h
    have hh := (C.same_x_iff hxa hxb).mp h
    rw [C.point_coordinates ha, C.point_coordinates hb] at hh
    exact hh.elim hne hneg
  refine ⟨hx, ?_⟩
  obtain ⟨R, slope, hc, hR, he⟩ := C.addition_complete hxa hxb hx
  have hn : a+b ≠ 0 := fun h => hneg (add_eq_zero_iff_eq_neg.mp h)
  have hRcoords : R = C.coordinates (a+b) := by
    apply C.point_injective (hP := hR) (hQ := C.coordinates_on_curve hn)
    simpa only [C.point_coordinates ha, C.point_coordinates hb, C.point_coordinates hn] using he
  exact ⟨slope, by simpa only [hRcoords] using hc⟩

omit [DecidableEq K] in
theorem coordinates_point {P : Coordinates K} (hP : C.OnCurve P) :
    C.coordinates (C.point P hP) = P := by
  cases P
  rfl

theorem coordinates_neg {g : C.Point} (hg : g ≠ 0) :
    C.coordinates (-g) = opposite (C.coordinates g) := by
  apply C.point_injective (hP := C.coordinates_on_curve (neg_ne_zero.mpr hg))
    (hQ := C.opposite_on_curve (C.coordinates_on_curve hg))
  rw [C.point_coordinates (neg_ne_zero.mpr hg), C.point_opposite (C.coordinates_on_curve hg), C.point_coordinates hg]

/-- Safe entries have a canonical table with exactly the paper's raw equations. -/
theorem canonical_table_checks {base : Coordinates K} (hbase : C.OnCurve base)
    {offset : C.Point} {steps : ℕ}
    (hsafe : TableSafe (C.point base hbase) offset steps) :
    TableChecks base (fun k => C.coordinates (entry (C.point base hbase) offset k)) steps := by
  intro k hk
  obtain ⟨_, slope, hc⟩ := C.coordinates_add_witnesses (hsafe.1 k (by omega))
    (C.point_ne_zero hbase) (hsafe.2 k hk).1 (hsafe.2 k hk).2
  refine ⟨slope, ?_⟩
  simpa only [entry_succ, C.coordinates_point hbase] using hc

/-- The existing initial table guard follows from offset admissibility. -/
theorem canonical_table_guard {base : Coordinates K} (hbase : C.OnCurve base)
    {offset : C.Point} {steps : ℕ} (hs : 0 < steps)
    (hsafe : TableSafe (C.point base hbase) offset steps) :
    base.x ≠ (C.coordinates offset).x := by
  have hn : -offset ≠ 0 := by simpa [entry] using hsafe.1 0 (by omega)
  have ho : offset ≠ 0 := neg_ne_zero.mp hn
  have hx := (C.coordinates_add_witnesses (hsafe.1 0 (by omega))
    (C.point_ne_zero hbase) (hsafe.2 0 hs).1 (hsafe.2 0 hs).2).1
  simpa only [entry, zero_nsmul, zero_sub, C.coordinates_neg ho, opposite, C.coordinates_point hbase] using hx.symm

/-- Witness existence tied to the sampled group seed; no semantic premises occur
inside TraceAccepts itself. -/
def TraceWitnesses (w l n : ℕ) (bases : ℕ → Coordinates K)
    (windows : ℕ → ℕ → ℕ) (u : C.Point) : Prop :=
  ∃ tr : CoordinateTrace K, C.TraceAccepts w l n bases windows tr ∧
    ∃ hu : C.OnCurve tr.seed, C.point tr.seed hu = u

/-- A successful group execution supplies the entire linked coordinate trace. -/
theorem trace_complete {w l n : ℕ} (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ) (u : C.Point)
    (haccept : GroupAccepts (2^w) l n (fun j => C.point (bases j) (hbases j)) windows u)
    (hbmap : Function.Injective (fun u : C.Point => 2^w • u))
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w) :
    C.TraceWitnesses w l n bases windows u := by
  let P := fun j => C.point (bases j) (hbases j)
  let V := (2^w-1) • u
  let boundary := fun i => C.coordinates (loop (2^w) l P windows u i)
  let doubles := fun i k => C.coordinates (2^k • loop (2^w) l P windows u i)
  let rows := fun i j => C.coordinates
    (addRows P (windows i) V (2^w • loop (2^w) l P windows u i) j)
  let table := fun j k => C.coordinates (entry (P j) V k)
  have hwidth : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  have hsteps : 0 < 2^w-1 := by omega
  have hu : u ≠ 0 := by intro h; exact haccept.1 (by simp [h])
  have hV : V ≠ 0 := by
    have h := (haccept.2.1 0 hl).1 0 (by omega)
    simpa only [entry, zero_nsmul, zero_sub, neg_ne_zero] using h
  have h0 : C.OnCurve (boundary 0) := C.coordinates_on_curve haccept.1
  have hn : C.OnCurve (boundary n) :=
    C.coordinates_on_curve (loop_ne_zero (2^w) l n P windows u haccept hbmap n (by omega))
  obtain ⟨offsetChain, hoc, hoe⟩ := C.scale_exists_to (C.coordinates_on_curve hu)
    (C.coordinates_on_curve hV) (2^w-1) (by rw [C.point_coordinates hV, C.point_coordinates hu])
  obtain ⟨initialChain, hic, hie⟩ := C.scale_exists_to (C.coordinates_on_curve hu)
    h0 l (by change C.point (C.coordinates (l • u)) h0 = _; rw [C.point_coordinates haccept.1, C.point_coordinates hu])
  obtain ⟨output, hfinal⟩ := C.complete_exists
    (show C.Valid (finiteEncoding (boundary n)) from fun _ => hn)
    (show C.Valid (finiteEncoding (opposite (boundary 0))) from fun _ => C.opposite_on_curve h0)
  let tr : CoordinateTrace K := {
    seed := C.coordinates u, offset := C.coordinates V, offsetChain := offsetChain,
    initialChain := initialChain, table := table, boundary := boundary,
    doubles := doubles, rows := rows, output := output }
  refine ⟨tr, ?_, C.coordinates_on_curve hu, C.point_coordinates hu⟩
  constructor
  · exact C.coordinates_on_curve hu
  · exact hoc
  · exact hoe
  · exact hic
  · exact hie
  · intro j _
    exact C.coordinates_neg hV
  · intro j hj
    exact C.canonical_table_guard (hbases j) hsteps (haccept.2.1 j hj)
  · intro j hj
    exact C.canonical_table_checks (hbases j) (haccept.2.1 j hj)
  · exact hrange
  · intro i _
    simp [tr, doubles, boundary]
  · intro i hi k hk
    exact C.msm_double_witnesses w l n P windows u haccept hbmap hi hk
  · intro i _
    rfl
  · intro i hi j hj
    simpa only [tr, rows, table, addRows] using
      C.msm_row_witnesses (2^w) l n P windows u haccept hbmap hrange hi hj
  · intro i _
    rfl
  · exact hfinal

end EfficientFFA.EllipticCurve.Curve
