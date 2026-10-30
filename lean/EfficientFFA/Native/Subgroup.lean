import EfficientFFA.Native.Statistics
import EfficientFFA.MSM.Subgroup
import EfficientFFA.EllipticCurve.Subgroup
open scoped ENNReal

namespace EfficientFFA.Native.ECEncoding
open EllipticCurve MSM
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)}
    (E : ECEncoding C n r) (H : AddSubgroup C.Point)

/-- Native trace soundness preserves membership of subgroup inputs. -/
theorem trace_output_mem_subgroup {w l t : ℕ} {bases : ℕ → Coordinates (ZMod q)}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace (ZMod q)}
    (hbases : ∀ j, C.OnCurve (bases j)) (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H)
    (ha : E.Trace w l t bases (descending windows t) tr) :
    ∃ hout : C.Valid tr.output, C.decode tr.output hout ∈ H :=
  C.trace_output_mem_subgroup H hbases hmem ((E.trace_iff _ _ _ _ _ _).mp ha)

/-- Native loading of a finite subgroup point: curve membership and a complete-add
chain for the subgroup-order scalar, whose endpoint is infinity. -/
def Member (P : Coordinates (ZMod q)) : Prop := E.OnCurve P ∧
  ∃ chain, E.Scale P chain (Nat.card H) ∧ E.Flag (chain (Nat.card H)).infinity true

theorem member_iff (hcop : (Nat.card (C.Point ⧸ H)).Coprime (Nat.card H))
    (P : Coordinates (ZMod q)) :
    E.Member H P ↔ ∃ hP : C.OnCurve P, C.point P hP ∈ H := by
  simp only [Member, E.onCurve_iff, E.scale_iff, E.flag_iff]
  constructor
  · rintro ⟨hP, hc⟩
    exact ⟨hP, (Subgroup.mem_iff_card_nsmul_eq_zero H hcop _).mpr ((C.scale_infinity_iff P hP _).mp hc)⟩
  · rintro ⟨hP, hm⟩
    exact ⟨hP, (C.scale_infinity_iff P hP _).mpr ((Subgroup.mem_iff_card_nsmul_eq_zero H hcop _).mp hm)⟩

variable [Fintype H] [DecidableEq H]

/-- Native-witness failure under normalized uniform sampling in a prime-order
subgroup. The ambient curve may have a nontrivial cofactor and two-torsion. -/
theorem uniform_subgroup_failure_bound (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H) (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ)) :
    (PMF.uniformOfFintype H).toOuterMeasure
      {u | ¬ E.TraceWitnesses w l t bases (descending windows t) (u : C.Point)} ≤
      (failureBudget (2^w) l t : ℝ≥0∞)/(Fintype.card H : ℝ≥0∞) := by
  simp only [E.traceWitnesses_iff]
  exact C.uniform_subgroup_trace_failure_bound_prime H w l t hw hl bases hbases hmem windows hrange hprime hsize

theorem exists_correct_subgroup_trace (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H) (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ))
    (hbudget : failureBudget (2^w) l t < Fintype.card H) :
    ∃ u : H, ∃ tr : CoordinateTrace (ZMod q), E.Trace w l t bases (descending windows t) tr ∧
      (∃ hs : C.OnCurve tr.seed, C.point tr.seed hs = (u : C.Point)) ∧
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
          C.point (bases j) (hbases j) ∧ C.decode tr.output hout ∈ H := by
  simp only [E.trace_iff]
  exact C.exists_correct_subgroup_trace H w l t hw hl bases hbases hmem windows hrange hprime hsize hbudget

/-- The input subgroup contract can itself be discharged by the native membership
checks, under the separate coprime-cofactor condition. -/
theorem uniform_subgroup_failure_bound_checked (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hmembers : ∀ j, E.Member H (bases j))
    (hcop : (Nat.card (C.Point ⧸ H)).Coprime (Nat.card H)) (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ)) :
    (PMF.uniformOfFintype H).toOuterMeasure
      {u | ¬ E.TraceWitnesses w l t bases (descending windows t) (u : C.Point)} ≤
      (failureBudget (2^w) l t : ℝ≥0∞)/(Fintype.card H : ℝ≥0∞) := by
  have hm := fun j => (E.member_iff H hcop (bases j)).mp (hmembers j)
  choose hbases hmem using hm
  exact E.uniform_subgroup_failure_bound H w l t hw hl bases hbases hmem windows hrange hprime hsize

end EfficientFFA.Native.ECEncoding
