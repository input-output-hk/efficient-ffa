import EfficientFFA.MSM.TraceStatistics
import EfficientFFA.MSM.Embedding
open scoped ENNReal

namespace EfficientFFA.EllipticCurve.Curve
open MSM
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K) (H : AddSubgroup C.Point)

/-- Subgroup membership of public bases is an explicit input contract. -/
def subgroupBases (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H) : ℕ → H :=
  fun j => ⟨C.point (bases j) (hbases j), hmem j⟩

/-- Construct a coordinate trace using radix injectivity only inside H.
No assumption is made about the order or finiteness of the ambient curve group. -/
theorem trace_complete_subgroup {w l n : ℕ} (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H)
    (windows : ℕ → ℕ → ℕ) (u : H)
    (ha : GroupAccepts (2^w) l n (C.subgroupBases H bases hbases hmem) windows u)
    (hbmap : Function.Injective (fun u : H => 2^w • u))
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w) :
    C.TraceWitnesses w l n bases windows (u : C.Point) := by
  have hg := (groupAccepts_map_iff H.subtype Subtype.val_injective (2^w) l n
    (C.subgroupBases H bases hbases hmem) windows u).mpr ha
  apply C.trace_complete_of_finite hw hl bases hbases windows (u : C.Point) hg ?_ hrange
  intro i hi k hk he
  have hn := doubling_ready w l n (C.subgroupBases H bases hbases hmem) windows u ha hbmap hi hk
  apply hn
  apply Subtype.val_injective
  change H.subtype (2^k • loop (2^w) l (C.subgroupBases H bases hbases hmem) windows u i) = H.subtype 0
  rw [map_nsmul, map_loop, map_zero]
  exact he

/-- Any accepted trace on subgroup bases returns a subgroup point, including infinity. -/
theorem trace_output_mem_subgroup {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (hbases : ∀ j, C.OnCurve (bases j)) (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H)
    (ha : C.TraceAccepts w l n bases (descending windows n) tr) :
    ∃ hout : C.Valid tr.output, C.decode tr.output hout ∈ H := by
  obtain ⟨hout, he⟩ := C.trace_sound_littleEndian hbases ha
  refine ⟨hout, ?_⟩
  rw [he]
  exact H.sum_mem (fun j _ => H.nsmul_mem (hmem j) _)

variable [Fintype H] [DecidableEq H]

/-- Sample uniformly from H itself (including zero), not from the ambient curve.
The denominator and all coefficient conditions use the subgroup order. -/
theorem uniform_subgroup_trace_failure_bound_prime (w l n : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H)
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ)) :
    (PMF.uniformOfFintype H).toOuterMeasure
      {u | ¬ C.TraceWitnesses w l n bases (descending windows n) (u : C.Point)} ≤
      (failureBudget (2^w) l n : ℝ≥0∞)/(Fintype.card H : ℝ≥0∞) := by
  have hb : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  have hm := prime_radix_injective (G := H) (2^w) l hb hl hprime hsize
  apply le_trans (show (PMF.uniformOfFintype H).toOuterMeasure
      {u | ¬ C.TraceWitnesses w l n bases (descending windows n) (u : C.Point)} ≤
      (PMF.uniformOfFintype H).toOuterMeasure
      {u | ¬ GroupAccepts (2^w) l n (C.subgroupBases H bases hbases hmem) (descending windows n) u} from ?_)
    (uniform_group_failure_bound_prime (2^w) l n hb hl _ _ hprime hsize)
  apply (PMF.uniformOfFintype H).toOuterMeasure.mono
  intro u hu hg
  exact hu (C.trace_complete_subgroup H hw hl bases hbases hmem _ u hg hm (descending_range hrange))

/-- Existence includes a seed in H, a correct MSM result and output membership. -/
theorem exists_correct_subgroup_trace (w l n : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H)
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ))
    (hbudget : failureBudget (2^w) l n < Fintype.card H) :
    ∃ u : H, ∃ tr : CoordinateTrace K, C.TraceAccepts w l n bases (descending windows n) tr ∧
      (∃ hs : C.OnCurve tr.seed, C.point tr.seed hs = (u : C.Point)) ∧
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range n, (2^w)^i*windows i j) •
          C.point (bases j) (hbases j) ∧ C.decode tr.output hout ∈ H := by
  have hb : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  obtain ⟨u, hu⟩ := exists_groupAccepts_prime (2^w) l n hb hl
    (C.subgroupBases H bases hbases hmem) (descending windows n) hprime hsize hbudget
  obtain ⟨tr, ht, hs⟩ := C.trace_complete_subgroup H hw hl bases hbases hmem _ u hu
    (prime_radix_injective (2^w) l hb hl hprime hsize) (descending_range hrange)
  obtain ⟨hout, he⟩ := C.trace_sound_littleEndian hbases ht
  refine ⟨u, tr, ht, hs, hout, he, ?_⟩
  rw [he]
  exact H.sum_mem (fun j _ => H.nsmul_mem (hmem j) _)

end EfficientFFA.EllipticCurve.Curve
