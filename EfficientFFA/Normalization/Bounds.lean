import EfficientFFA.Normalization.Definitions

namespace EfficientFFA.Normalization

/-- Linear bounds from signed inputs and ordinary output limbs. The lower
bound is the paper's -(limit+B) coefficient sum (slightly conservative). -/
theorem weighted_linear_bounds {n : ℕ} {B limit : ℤ} (c x z : Limbs n)
    (hc : ∀ i, 0 ≤ c i)
    (hx : LazyArithmetic.Bounded (fun _ => -limit) (fun _ => limit) x)
    (hz : WellFormed B z) :
    -(limit+B) * (∑ i, c i) ≤ (∑ i, c i * x i) - ∑ i, c i * z i ∧
      (∑ i, c i * x i) - ∑ i, c i * z i ≤ limit * ∑ i, c i := by
  have hl : (∑ i, c i * (-limit)) ≤ ∑ i, c i * x i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i).1 (hc i)
  have hu : (∑ i, c i * x i) ≤ ∑ i, c i * limit :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i).2 (hc i)
  have hz' := Multiplication.weighted_sum_bounds c z hc hz
  have hs : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  rw [← Finset.sum_mul] at hl hu
  constructor <;> nlinarith

namespace Parameters
variable {n r : ℕ} {P : Parameters n r}

theorem residual_bounds (hP : P.Positive) {x z : Limbs n}
    (hx : P.InputBounded x) (hz : WellFormed P.B z) :
    -P.A ≤ residual P.B P.q x z ∧ residual P.B P.q x z ≤ P.C := by
  have h := weighted_linear_bounds P.singleCoeff x z
    (fun _ => Int.emod_nonneg _ (ne_of_gt hP.foreign)) hx hz
  simpa only [A, C, singleCoeff, residual, neg_mul] using h

theorem auxCore_bounds (hP : P.Positive) {x z : Limbs n} {u : ℤ}
    (hx : P.InputBounded x) (hz : WellFormed P.B z)
    (hu : 0 ≤ u ∧ u < P.Umax) (a : Fin r) :
    -P.Am a ≤ P.auxCore x z u a ∧ P.auxCore x z u a ≤ P.Cm a := by
  have hb := weighted_linear_bounds (fun i => P.singleCoeff i % P.M a) x z
    (fun _ => Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))) hx hz
  have hq : 0 ≤ P.q % P.M a := Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))
  have huq := mul_le_mul_of_nonneg_right (le_of_lt hu.2) hq
  have huq0 := mul_nonneg hu.1 hq
  dsimp [auxCore, Am, Cm]
  constructor <;> linarith

theorem nativeResidual_bounds (hP : P.Positive) {x z : Limbs n} {u : ℤ}
    (hx : P.InputBounded x) (hz : WellFormed P.B z)
    (hu : 0 ≤ u ∧ u < P.Umax) :
    -P.A - (P.Umax + P.kmin) * P.q ≤ P.nativeResidual x z u ∧
      P.nativeResidual x z u ≤ P.C - P.kmin * P.q := by
  have hd := P.residual_bounds hP hx hz
  have hq := hP.foreign
  dsimp [nativeResidual]
  constructor <;> nlinarith

theorem auxResidual_bounds (hP : P.Positive) {x z : Limbs n} {u v : ℤ}
    (hx : P.InputBounded x) (hz : WellFormed P.B z)
    (hu : 0 ≤ u ∧ u < P.Umax) (a : Fin r) (hv : 0 ≤ v ∧ v < P.Vmax a) :
    P.auxLower a ≤ P.auxResidual x z u v a ∧
      P.auxResidual x z u v a ≤ P.auxUpper a := by
  have he := P.auxCore_bounds hP hx hz hu a
  have hm := hP.auxiliary a
  dsimp [auxLower, auxUpper, auxResidual]
  constructor <;> nlinarith

end Parameters
end EfficientFFA.Normalization
