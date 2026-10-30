import EfficientFFA.ShiftedEncoding.Multiplication.Definitions

namespace EfficientFFA.ShiftedEncoding.Multiplication
open EfficientFFA.Multiplication (weighted_sum_bounds weighted_product_bounds)

namespace Parameters
variable {n r : ℕ} {P : Parameters n r}

theorem residual_bounds (hP : P.Positive) {x y z : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z) :
    -P.A ≤ residual P.B P.q x y z ∧ residual P.B P.q x y z ≤ P.C := by
  have hc : ∀ i, 0 ≤ P.singleCoeff i :=
    fun i => Int.emod_nonneg _ (ne_of_gt hP.foreign)
  have hd : ∀ i j, 0 ≤ P.doubleCoeff i j :=
    fun i j => Int.emod_nonneg _ (ne_of_gt hP.foreign)
  have hsx := weighted_sum_bounds P.singleCoeff x hc hx
  have hsy := weighted_sum_bounds P.singleCoeff y hc hy
  have hs := weighted_sum_bounds P.singleCoeff z hc hz
  have hp := weighted_product_bounds P.doubleCoeff x y hP.radix hd hx hy
  change -P.A ≤ _ ∧ _ ≤ P.C
  dsimp [A, C, singleCoeff, doubleCoeff] at hsx hsy hs hp ⊢
  unfold residual
  constructor <;> linarith

theorem auxCore_bounds (hP : P.Positive) {x y z : Limbs n} {u : ℤ}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hu : 0 ≤ u ∧ u < P.Umax) (a : Fin r) :
    -P.Am a ≤ P.auxCore x y z u a ∧ P.auxCore x y z u a ≤ P.Cm a := by
  have hc : ∀ i, 0 ≤ P.singleCoeff i % P.M a :=
    fun i => Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))
  have hd : ∀ i j, 0 ≤ P.doubleCoeff i j % P.M a :=
    fun i j => Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))
  have hsx := weighted_sum_bounds (fun i => P.singleCoeff i % P.M a) x hc hx
  have hsy := weighted_sum_bounds (fun i => P.singleCoeff i % P.M a) y hc hy
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
end EfficientFFA.ShiftedEncoding.Multiplication
