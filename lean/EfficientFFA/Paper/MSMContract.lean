import EfficientFFA.Paper

namespace EfficientFFA.Paper
open EllipticCurve Native MSM
open scoped ENNReal

variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

/-- The corrected thm:msm in one statement: universal soundness, a finite
uniform failure bound, and existence when that bound's numerator is below N.
Arithmetic validity is carried by E; group size and sampling assumptions are
separate. There are no added table-internal guard hypotheses. -/
theorem msm_contract [Fintype C.Point] [DecidableEq C.Point]
    (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card C.Point : ℤ)) :
    (∀ tr : CoordinateTrace (ZMod q),
      E.Trace w l t bases (descending windows t) tr →
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
          C.point (bases j) (hbases j)) ∧
    ((PMF.uniformOfFintype C.Point).toOuterMeasure
      {u | ¬ E.TraceWitnesses w l t bases (descending windows t) u} ≤
      ((1+l*(2^w+1)+2*t*l : ℕ) : ℝ≥0∞)/(Fintype.card C.Point : ℝ≥0∞)) ∧
    (1+l*(2^w+1)+2*t*l < Fintype.card C.Point →
      ∃ tr : CoordinateTrace (ZMod q), E.Trace w l t bases (descending windows t) tr ∧
        ∃ hout : C.Valid tr.output, C.decode tr.output hout =
          ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
            C.point (bases j) (hbases j)) := by
  exact ⟨fun _ ha => msm_sound E hbases ha,
    msm_failure_bound E w l t hw hl bases hbases windows hrange hprime hsize,
    msm_exists_correct E w l t hw hl bases hbases windows hrange hprime hsize⟩

/-- The same combined contract when randomness is uniform in a prime-order
subgroup. The existence conclusion records the seed and output membership. -/
theorem msm_subgroup_contract (H : AddSubgroup C.Point) [Fintype H] [DecidableEq H]
    (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H) (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ)) :
    (∀ tr : CoordinateTrace (ZMod q),
      E.Trace w l t bases (descending windows t) tr →
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
          C.point (bases j) (hbases j)) ∧
    ((PMF.uniformOfFintype H).toOuterMeasure
      {u | ¬ E.TraceWitnesses w l t bases (descending windows t) (u : C.Point)} ≤
      ((1+l*(2^w+1)+2*t*l : ℕ) : ℝ≥0∞)/(Fintype.card H : ℝ≥0∞)) ∧
    (1+l*(2^w+1)+2*t*l < Fintype.card H →
      ∃ u : H, ∃ tr : CoordinateTrace (ZMod q), E.Trace w l t bases (descending windows t) tr ∧
        (∃ hs : C.OnCurve tr.seed, C.point tr.seed hs = (u : C.Point)) ∧
        ∃ hout : C.Valid tr.output, C.decode tr.output hout =
          ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
            C.point (bases j) (hbases j) ∧ C.decode tr.output hout ∈ H) := by
  exact ⟨fun _ ha => msm_sound E hbases ha,
    msm_subgroup_failure_bound E H w l t hw hl bases hbases hmem windows hrange hprime hsize,
    msm_exists_correct_subgroup E H w l t hw hl bases hbases hmem windows hrange hprime hsize⟩

end EfficientFFA.Paper
