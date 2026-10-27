import EfficientFFA.Native.Trace
open scoped ENNReal

namespace EfficientFFA.Native.ECEncoding
open EllipticCurve MSM
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

def TraceWitnesses (w l t : ℕ) (bases : ℕ → Coordinates (ZMod q))
    (windows : ℕ → ℕ → ℕ) (u : C.Point) : Prop :=
  ∃ tr, E.Trace w l t bases windows tr ∧
    ∃ hu : C.OnCurve tr.seed, C.point tr.seed hu = u

theorem traceWitnesses_iff (w l t : ℕ) (bases : ℕ → Coordinates (ZMod q))
    (windows : ℕ → ℕ → ℕ) (u : C.Point) :
    E.TraceWitnesses w l t bases windows u ↔ C.TraceWitnesses w l t bases windows u := by
  simp only [TraceWitnesses, Curve.TraceWitnesses, E.trace_iff]

variable [Fintype C.Point] [DecidableEq C.Point]

/-- Statistical completeness now concerns existence of native arithmetic witnesses. -/
theorem uniform_littleEndian_failure_bound (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card C.Point : ℤ)) :
    (PMF.uniformOfFintype C.Point).toOuterMeasure
      {u | ¬ E.TraceWitnesses w l t bases (descending windows t) u} ≤
      (failureBudget (2^w) l t : ℝ≥0∞) / (Fintype.card C.Point : ℝ≥0∞) := by
  simp only [E.traceWitnesses_iff]
  exact C.uniform_littleEndian_trace_failure_bound_prime w l t hw hl bases hbases windows hrange hprime hsize

/-- A native arithmetic witness exists and its decoded output is the requested MSM. -/
theorem exists_correct_trace (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card C.Point : ℤ))
    (hbudget : failureBudget (2^w) l t < Fintype.card C.Point) :
    ∃ tr : CoordinateTrace (ZMod q), E.Trace w l t bases (descending windows t) tr ∧
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
          C.point (bases j) (hbases j) := by
  simp only [E.trace_iff]
  exact C.exists_correct_trace_prime w l t hw hl bases hbases windows hrange hprime hsize hbudget

end EfficientFFA.Native.ECEncoding
