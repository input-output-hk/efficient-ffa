import EfficientFFA.MSM.Chains

namespace EfficientFFA.Subgroup
variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G)

/-- An order-multiplication test characterizes H when its order is coprime to
the quotient order. Prime order of H alone would not justify this test. -/
theorem mem_iff_card_nsmul_eq_zero
    (hcop : (Nat.card (G ⧸ H)).Coprime (Nat.card H)) (x : G) :
    x ∈ H ↔ Nat.card H • x = 0 := by
  constructor
  · intro hx
    have h : Nat.card H • (⟨x,hx⟩ : H) = 0 := card_nsmul_eq_zero'
    exact congrArg H.subtype h
  · intro hx
    apply (QuotientAddGroup.eq_zero_iff x).mp
    apply (hcop.nsmul_right_bijective (G := G ⧸ H)).injective
    simpa using congrArg (QuotientAddGroup.mk' H) hx

end EfficientFFA.Subgroup

namespace EfficientFFA.EllipticCurve.Curve
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

/-- Complete-add chains turn a fixed-scalar zero test into coordinate constraints. -/
theorem scale_infinity_iff (P : Coordinates K) (hP : C.OnCurve P) (n : ℕ) :
    (∃ chain, C.ScaleChecks P chain n ∧ (chain n).infinity = true) ↔ n • C.point P hP = 0 := by
  constructor
  · rintro ⟨chain, hc, hinf⟩
    obtain ⟨hv, he⟩ := C.scale_sound hP hc n (by omega)
    exact he.symm.trans (C.decode_infinity hv hinf)
  · intro hz
    obtain ⟨chain, hc⟩ := C.scale_exists P hP n
    obtain ⟨hv, he⟩ := C.scale_sound hP hc n (by omega)
    refine ⟨chain, hc, ?_⟩
    cases hb : (chain n).infinity
    · have hp := C.point_ne_zero (hv hb)
      exact False.elim (hp ((C.decode_finite hv hb).symm.trans (he.trans hz)))
    · rfl

end EfficientFFA.EllipticCurve.Curve
