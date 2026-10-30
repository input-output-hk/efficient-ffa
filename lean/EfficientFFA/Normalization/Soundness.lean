import EfficientFFA.Normalization.Bounds

namespace EfficientFFA.Normalization.Parameters
variable {n r : ℕ} (P : Parameters n r)

/-- Reducing coefficients in the auxiliary expression preserves the original
native residual modulo that auxiliary modulus. -/
theorem auxCore_congr (x z : Limbs n) (u : ℤ) (a : Fin r) :
    P.auxCore x z u a ≡ P.nativeResidual x z u [ZMOD P.M a] := by
  dsimp [Int.ModEq, auxCore, nativeResidual, residual, singleCoeff]
  rw [add_mul, sub_add_eq_sub_sub]
  simp [Int.sub_emod, Int.mul_emod, Finset.sum_int_mod]

/-- Soundness of the actual native-field constraints. Width adequacy is
needed for completeness, not for soundness of already bounded witnesses. -/
theorem normalization_sound (hP : P.Positive) (hnw : P.NoWrap)
    {x z : Limbs n} {u : ℤ} {v : Fin r → ℤ}
    (hx : P.InputBounded x) (hz : WellFormed P.B z)
    (hacc : P.Accepts x z u v) :
    eval P.B x ≡ eval P.B z [ZMOD P.q] := by
  have haux : ∀ a, P.auxResidual x z u (v a) a = 0 := by
    intro a
    have hb := P.auxResidual_bounds hP hx hz hacc.u_range a (hacc.v_range a)
    exact eq_zero_of_modEq_of_bounds (hacc.auxiliary a)
      (lt_of_lt_of_le (hnw.auxiliary_lower a) hb.1)
      (lt_of_le_of_lt hb.2 (hnw.auxiliary_upper a))
  have hm : ∀ a, P.nativeResidual x z u ≡ 0 [ZMOD P.M a] := by
    intro a
    have hd : P.M a ∣ P.auxCore x z u a := by
      refine ⟨v a + P.lmin a, ?_⟩
      have h := haux a
      dsimp [auxResidual] at h
      nlinarith
    exact (P.auxCore_congr x z u a).symm.trans (Int.modEq_zero_iff_dvd.mpr hd)
  have hall : ∀ m ∈ P.moduli, P.nativeResidual x z u ≡ 0 [ZMOD m] := by
    intro m hmem
    simp only [moduli, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact hacc.native
    · rcases List.mem_ofFn.mp hmem with ⟨a, rfl⟩
      exact hm a
  have hb := P.nativeResidual_bounds hP hx hz hacc.u_range
  have hzero : P.nativeResidual x z u = 0 := by
    apply eq_zero_of_congruences_of_bounds hall
    · change -P.L < P.nativeResidual x z u
      have := hnw.reconstruction_lower
      linarith
    · change P.nativeResidual x z u < P.L
      exact lt_of_le_of_lt hb.2 hnw.reconstruction_upper
  apply (normalization_iff_quotient P.B P.q x z).mpr
  exact ⟨u + P.kmin, sub_eq_zero.mp hzero⟩

end EfficientFFA.Normalization.Parameters
