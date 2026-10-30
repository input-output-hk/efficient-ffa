import EfficientFFA.Multiplication.Definitions

namespace EfficientFFA.Multiplication

/-- A bounded weighted sum, keeping the coefficient sum instead of replacing
it with a coarse count-times-modulus estimate. -/
theorem weighted_sum_bounds {n : ℕ} {B : ℤ} (c x : Fin n → ℤ)
    (hc : ∀ i, 0 ≤ c i) (hx : WellFormed B x) :
    0 ≤ ∑ i, c i * x i ∧ (∑ i, c i * x i) ≤ (B-1) * ∑ i, c i := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hx i).1
  · calc
      (∑ i, c i * x i) ≤ ∑ i, (B-1)*c i := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hx i
        have hci := hc i
        have hxi : x i ≤ B-1 := by omega
        nlinarith
      _ = (B-1) * ∑ i, c i := by rw [Finset.mul_sum]

theorem weighted_product_bounds {n : ℕ} {B : ℤ} (c : Fin n → Fin n → ℤ)
    (x y : Limbs n) (hB : 0 < B) (hc : ∀ i j, 0 ≤ c i j)
    (hx : WellFormed B x) (hy : WellFormed B y) :
    0 ≤ (∑ i, ∑ j, c i j * x i * y j) ∧
    (∑ i, ∑ j, c i j * x i * y j) ≤ (B-1)^2 * ∑ i, ∑ j, c i j := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hc i j) (hx i).1) (hy j).1
  · calc
      (∑ i, ∑ j, c i j * x i * y j) ≤ ∑ i, ∑ j, (B-1)^2 * c i j := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have hx' : x i ≤ B-1 := by have := hx i; omega
        have hy' : y j ≤ B-1 := by have := hy j; omega
        have hprod : x i * y j ≤ (B-1)^2 := by
          have := mul_le_mul hx' hy' (hy j).1 (by omega : 0 ≤ B-1)
          nlinarith
        have := mul_le_mul_of_nonneg_left hprod (hc i j)
        nlinarith
      _ = (B-1)^2 * ∑ i, ∑ j, c i j := by simp only [Finset.mul_sum]

/-- The lower endpoint is a ceiling, expressed by negating a floor of the
positive lower-bound magnitude. This also handles negative quotients. -/
theorem quotient_interval {A C d k : ℤ} (hd : 0 < d)
    (hlo : -A ≤ k*d) (hhi : k*d ≤ C) : -(A/d) ≤ k ∧ k ≤ C/d := by
  have hneg : -k ≤ A/d := (Int.le_ediv_iff_mul_le hd).mpr (by nlinarith)
  exact ⟨by omega, (Int.le_ediv_iff_mul_le hd).mpr hhi⟩

namespace Parameters
variable {n r : ℕ} {P : Parameters n r}

theorem residual_bounds (hP : P.Positive) {x y z : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z) :
    -P.A ≤ mulResidual P.B P.q x y z ∧ mulResidual P.B P.q x y z ≤ P.C := by
  have hc : ∀ i, 0 ≤ P.singleCoeff i :=
    fun i => Int.emod_nonneg _ (ne_of_gt hP.foreign)
  have hd : ∀ i j, 0 ≤ P.doubleCoeff i j :=
    fun i j => Int.emod_nonneg _ (ne_of_gt hP.foreign)
  have hs := weighted_sum_bounds P.singleCoeff z hc hz
  have hp := weighted_product_bounds P.doubleCoeff x y hP.radix hd hx hy
  change -P.A ≤ _ ∧ _ ≤ P.C
  dsimp [A, C, singleCoeff, doubleCoeff] at hs hp ⊢
  unfold mulResidual
  constructor <;> linarith

theorem auxCore_bounds (hP : P.Positive) {x y z : Limbs n} {u : ℤ}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hu : 0 ≤ u ∧ u < P.Umax) (a : Fin r) :
    -P.Am a ≤ P.auxCore x y z u a ∧ P.auxCore x y z u a ≤ P.Cm a := by
  have hc : ∀ i, 0 ≤ P.singleCoeff i % P.M a :=
    fun i => Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))
  have hd : ∀ i j, 0 ≤ P.doubleCoeff i j % P.M a :=
    fun i j => Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))
  have hs := weighted_sum_bounds (fun i => P.singleCoeff i % P.M a) z hc hz
  have hp := weighted_product_bounds (fun i j => P.doubleCoeff i j % P.M a)
    x y hP.radix hd hx hy
  have hq : 0 ≤ P.q % P.M a := Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))
  have huq := mul_le_mul_of_nonneg_right (le_of_lt hu.2) hq
  have huq0 := mul_nonneg hu.1 hq
  dsimp [auxCore, Am, Cm]
  constructor <;> linarith

theorem nativeResidual_bounds (hP : P.Positive) {x y z : Limbs n} {u : ℤ}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hu : 0 ≤ u ∧ u < P.Umax) :
    -P.A - (P.Umax + P.kmin) * P.q ≤ P.nativeResidual x y z u ∧
      P.nativeResidual x y z u ≤ P.C - P.kmin * P.q := by
  have hd := P.residual_bounds hP hx hy hz
  have hq := hP.foreign
  dsimp [nativeResidual]
  constructor <;> nlinarith

theorem auxResidual_bounds (hP : P.Positive) {x y z : Limbs n} {u v : ℤ}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hu : 0 ≤ u ∧ u < P.Umax) (a : Fin r) (hv : 0 ≤ v ∧ v < P.Vmax a) :
    P.auxLower a ≤ P.auxResidual x y z u v a ∧
      P.auxResidual x y z u v a ≤ P.auxUpper a := by
  have he := P.auxCore_bounds hP hx hy hz hu a
  have hm := hP.auxiliary a
  dsimp [auxLower, auxUpper, auxResidual]
  constructor <;> nlinarith

end Parameters
end EfficientFFA.Multiplication
