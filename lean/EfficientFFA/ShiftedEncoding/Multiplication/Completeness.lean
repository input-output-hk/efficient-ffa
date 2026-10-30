import EfficientFFA.ShiftedEncoding.Multiplication.Soundness

namespace EfficientFFA.ShiftedEncoding.Multiplication.Parameters
open EfficientFFA.Multiplication (quotient_interval)
variable {n r : ℕ} (P : Parameters n r)

/-- The native quotient shifted into its nonnegative witness interval. -/
def witnessU (x y z : Limbs n) : ℤ :=
  residual P.B P.q x y z / P.q - P.kmin

/-- Each auxiliary quotient, shifted independently by its lower bound. -/
def witnessV (x y z : Limbs n) (a : Fin r) : ℤ :=
  P.auxCore x y z (P.witnessU x y z) a / P.M a - P.lmin a

/-- Correct modular products have explicitly constructed accepting witnesses.
No reconstruction or no-wrap hypotheses are needed in this direction. -/
theorem canonical_witnesses_accept (hP : P.Positive) (hw : P.WidthBounds)
    {x y z : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hmul : value P.B x * value P.B y ≡ value P.B z [ZMOD P.q]) :
    P.Accepts x y z (P.witnessU x y z) (P.witnessV x y z) := by
  have hd := (residual_dvd_iff P.B P.q x y z).mpr hmul
  have hk := Int.ediv_mul_cancel hd
  have hb := P.residual_bounds hP hx hy hz
  have hki := quotient_interval hP.foreign
    (show -P.A ≤ (residual P.B P.q x y z / P.q) * P.q by omega)
    (show (residual P.B P.q x y z / P.q) * P.q ≤ P.C by omega)
  have hu : 0 ≤ P.witnessU x y z ∧ P.witnessU x y z < P.Umax := by
    have hwidth := hw.native
    dsimp [witnessU, kmin, kmax] at *
    omega
  have hn : P.nativeResidual x y z (P.witnessU x y z) = 0 := by
    dsimp [nativeResidual, witnessU]
    rw [sub_add_cancel, hk, sub_self]
  have ha : ∀ a, (0 ≤ P.witnessV x y z a ∧ P.witnessV x y z a < P.Vmax a) ∧
      P.auxResidual x y z (P.witnessU x y z) (P.witnessV x y z a) a = 0 := by
    intro a
    have hc : P.auxCore x y z (P.witnessU x y z) a ≡ 0 [ZMOD P.M a] := by
      simpa only [hn] using P.auxCore_congr x y z (P.witnessU x y z) a
    have hl := Int.ediv_mul_cancel (Int.modEq_zero_iff_dvd.mp hc)
    have hab := P.auxCore_bounds hP hx hy hz hu a
    have hli := quotient_interval (hP.auxiliary a)
      (show -P.Am a ≤ (P.auxCore x y z (P.witnessU x y z) a / P.M a) * P.M a by omega)
      (show (P.auxCore x y z (P.witnessU x y z) a / P.M a) * P.M a ≤ P.Cm a by omega)
    constructor
    · have hwidth := hw.auxiliary a
      dsimp [witnessV, lmin, lmax] at *
      omega
    · dsimp [auxResidual, witnessV]
      rw [sub_add_cancel, hl, sub_self]
  exact ⟨hu, fun a => (ha a).1, by simp [hn], fun a => by simp [(ha a).2]⟩

/-- Existential completeness, with the witnesses supplied by the explicit constructors. -/
theorem multiplication_complete (hP : P.Positive) (hw : P.WidthBounds)
    {x y z : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hmul : value P.B x * value P.B y ≡ value P.B z [ZMOD P.q]) :
    ∃ u v, P.Accepts x y z u v :=
  ⟨P.witnessU x y z, P.witnessV x y z,
    P.canonical_witnesses_accept hP hw hx hy hz hmul⟩

end EfficientFFA.ShiftedEncoding.Multiplication.Parameters
