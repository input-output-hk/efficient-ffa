import EfficientFFA.MSM.TraceCompleteness
open scoped ENNReal

namespace EfficientFFA.MSM
/-- Reversing window order preserves the lookup range checks. -/
theorem descending_range {b l n : ℕ} {windows : ℕ → ℕ → ℕ}
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < b) :
    ∀ i, i < n → ∀ j, j < l → descending windows n i j < b := by
  intro i hi j hj
  exact hrange (n-1-i) (by omega) j hj
end EfficientFFA.MSM

namespace EfficientFFA.EllipticCurve.Curve
open MSM
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)
variable [Fintype C.Point] [DecidableEq C.Point]

/-- Statistical completeness of the whole coordinate trace under explicit
prime-group parameter bounds and normalized uniform seed sampling. -/
theorem uniform_trace_failure_bound_prime (w l n : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w)
    (hq : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)* (l : ℤ) + (2^w : ℕ)-1 < (Nat.card C.Point : ℤ)) :
    (PMF.uniformOfFintype C.Point).toOuterMeasure
      {u | ¬ C.TraceWitnesses w l n bases windows u} ≤
      (failureBudget (2^w) l n : ℝ≥0∞) / (Fintype.card C.Point : ℝ≥0∞) := by
  have hb : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  have hbmap := prime_radix_injective (G := C.Point) (2^w) l hb hl hq hsize
  apply le_trans (show (PMF.uniformOfFintype C.Point).toOuterMeasure
      {u | ¬ C.TraceWitnesses w l n bases windows u} ≤
      (PMF.uniformOfFintype C.Point).toOuterMeasure
      {u | ¬ GroupAccepts (2^w) l n (fun j => C.point (bases j) (hbases j)) windows u} from ?_)
    (uniform_group_failure_bound_prime (2^w) l n hb hl _ windows hq hsize)
  apply (PMF.uniformOfFintype C.Point).toOuterMeasure.mono
  intro u hu hg
  exact hu (C.trace_complete hw hl bases hbases windows u hg hbmap hrange)

/-- The probability theorem for the corrected little-endian traversal. -/
theorem uniform_littleEndian_trace_failure_bound_prime (w l n : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w)
    (hq : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)* (l : ℤ) + (2^w : ℕ)-1 < (Nat.card C.Point : ℤ)) :
    (PMF.uniformOfFintype C.Point).toOuterMeasure
      {u | ¬ C.TraceWitnesses w l n bases (descending windows n) u} ≤
      (failureBudget (2^w) l n : ℝ≥0∞) / (Fintype.card C.Point : ℝ≥0∞) :=
  C.uniform_trace_failure_bound_prime w l n hw hl bases hbases (descending windows n)
    (descending_range hrange) hq hsize

/-- A budget strictly below group size supplies an accepted coordinate trace. -/
theorem exists_trace_prime (w l n : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w)
    (hq : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)* (l : ℤ) + (2^w : ℕ)-1 < (Nat.card C.Point : ℤ))
    (hbudget : failureBudget (2^w) l n < Fintype.card C.Point) :
    ∃ u : C.Point, C.TraceWitnesses w l n bases windows u := by
  have hb : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  obtain ⟨u, hu⟩ := exists_groupAccepts_prime (2^w) l n hb hl
    (fun j => C.point (bases j) (hbases j)) windows hq hsize hbudget
  exact ⟨u, C.trace_complete hw hl bases hbases windows u hu
    (prime_radix_injective (2^w) l hb hl hq hsize) hrange⟩

/-- Combined existence and soundness endpoint for little-endian scalar inputs. -/
theorem exists_correct_trace_prime (w l n : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w)
    (hq : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)* (l : ℤ) + (2^w : ℕ)-1 < (Nat.card C.Point : ℤ))
    (hbudget : failureBudget (2^w) l n < Fintype.card C.Point) :
    ∃ tr : CoordinateTrace K, C.TraceAccepts w l n bases (descending windows n) tr ∧
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range n, (2^w)^i * windows i j) •
          C.point (bases j) (hbases j) := by
  obtain ⟨_, tr, ha, _⟩ := C.exists_trace_prime w l n hw hl bases hbases
    (descending windows n) (descending_range hrange) hq hsize hbudget
  exact ⟨tr, ha, C.trace_sound_littleEndian hbases ha⟩

end EfficientFFA.EllipticCurve.Curve
