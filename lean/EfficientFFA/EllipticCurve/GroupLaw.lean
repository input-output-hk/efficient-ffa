import EfficientFFA.EllipticCurve.Affine

namespace EfficientFFA.EllipticCurve
namespace Curve
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

omit [DecidableEq K] in
theorem result_x (P Q : Coordinates K) (slope : K) :
    (result P Q slope).x = C.W.addX P.x Q.x slope := by
  simp [result, W, model, WeierstrassCurve.Affine.addX]

omit [DecidableEq K] in
theorem result_y (P Q : Coordinates K) (slope : K) :
    (result P Q slope).y = C.W.addY P.x Q.x P.y slope := by
  simp [result, W, model, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX]
  ring

theorem slope_chord {P Q : Coordinates K} (hne : P.x ≠ Q.x) :
    C.W.slope P.x Q.x P.y Q.y = chord P Q := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
  dsimp [chord]
  field_simp [sub_ne_zero.mpr hne, sub_ne_zero.mpr hne.symm]
  ring

omit [DecidableEq K] in
theorem y_ne_neg_of_den {P : Coordinates K} (hden : 2*P.y ≠ 0) :
    P.y ≠ C.W.negY P.x P.y := by
  simp only [WeierstrassCurve.Affine.negY, W, model, zero_mul, sub_zero]
  intro h
  apply hden
  linear_combination h

theorem slope_tangent {P : Coordinates K} (hden : 2*P.y ≠ 0) :
    C.W.slope P.x P.x P.y P.y = tangent C P := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (C.y_ne_neg_of_den hden)]
  simp only [tangent, W, model, WeierstrassCurve.Affine.negY, zero_mul, mul_zero,
    add_zero, sub_zero, sub_neg_eq_add, ← two_mul]

/-- The closed-form output is on the curve and is the concrete group sum. -/
theorem result_group {P Q : Coordinates K} (hP : C.OnCurve P) (hQ : C.OnCurve Q)
    (hno : ¬ (P.x = Q.x ∧ P.y = C.W.negY Q.x Q.y)) {slope : K}
    (hs : C.W.slope P.x Q.x P.y Q.y = slope) :
    ∃ hR : C.OnCurve (result P Q slope),
      C.point (result P Q slope) hR = C.point P hP + C.point Q hQ := by
  have hns := WeierstrassCurve.Affine.nonsingular_add (C.nonsingular hP) (C.nonsingular hQ) hno
  have hRns : C.W.Nonsingular (result P Q slope).x (result P Q slope).y := by
    rw [C.result_x, C.result_y, ← hs]
    exact hns
  refine ⟨(C.equation_iff _).mp hRns.1, ?_⟩
  unfold point
  rw [WeierstrassCurve.Affine.Point.add_some hno]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  rw [C.result_x, C.result_y, hs]
  exact ⟨rfl, rfl⟩

theorem addition_sound {P Q R : Coordinates K} {slope : K}
    (hP : C.OnCurve P) (hQ : C.OnCurve Q) (hne : P.x ≠ Q.x)
    (hc : AddChecks P Q R slope) :
    ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point Q hQ := by
  obtain ⟨hs, rfl⟩ := (add_checks_iff hne).mp hc
  exact C.result_group hP hQ (fun h => hne h.1) ((C.slope_chord hne).trans hs.symm)

theorem addition_complete {P Q : Coordinates K} (hP : C.OnCurve P) (hQ : C.OnCurve Q)
    (hne : P.x ≠ Q.x) :
    ∃ R slope, AddChecks P Q R slope ∧
      ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point Q hQ := by
  have hc : AddChecks P Q (result P Q (chord P Q)) (chord P Q) :=
    (add_checks_iff hne).mpr ⟨rfl, rfl⟩
  exact ⟨_, _, hc, C.addition_sound hP hQ hne hc⟩

omit [DecidableEq K] in
/-- At a smooth point, an accepted tangent equation implies its denominator
is nonzero. No extra denominator check is needed for soundness. -/
theorem double_den_ne {P R : Coordinates K} {slope : K}
    (hP : C.OnCurve P) (hc : DoubleChecks C P R slope) : 2*P.y ≠ 0 := by
  intro hz
  have ht : 3*P.x^2+C.a = 0 := by
    have h := hc.slope_eq
    rw [hz, zero_mul, sub_zero] at h
    exact h
  have hn := (WeierstrassCurve.Affine.nonsingular_iff' P.x P.y).mp (C.nonsingular hP)
  simp only [W, model, zero_mul, mul_zero, add_zero, zero_sub] at hn
  exact hn.2.elim (fun h => h (by rw [ht, neg_zero])) (fun h => h hz)

theorem doubling_sound {P R : Coordinates K} {slope : K}
    (hP : C.OnCurve P) (hc : DoubleChecks C P R slope) :
    ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point P hP := by
  have hd := C.double_den_ne hP hc
  obtain ⟨hs, rfl⟩ := (double_checks_iff hd).mp hc
  exact C.result_group hP hP (fun h => C.y_ne_neg_of_den hd h.2)
    ((C.slope_tangent hd).trans hs.symm)

theorem doubling_complete {P : Coordinates K} (hP : C.OnCurve P) (hden : 2*P.y ≠ 0) :
    ∃ R slope, DoubleChecks C P R slope ∧
      ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point P hP := by
  have hc : DoubleChecks C P (result P P (tangent C P)) (tangent C P) :=
    (double_checks_iff hden).mpr ⟨rfl, rfl⟩
  exact ⟨_, _, hc, C.doubling_sound hP hc⟩

/-- Exactly the finite points with nonzero tangent denominator admit these witnesses. -/
theorem doubling_witnesses_iff {P : Coordinates K} (hP : C.OnCurve P) :
    (∃ R slope, DoubleChecks C P R slope) ↔ 2*P.y ≠ 0 := by
  constructor
  · rintro ⟨R, slope, hc⟩
    exact C.double_den_ne hP hc
  · intro hd
    obtain ⟨R, slope, hc, _⟩ := C.doubling_complete hP hd
    exact ⟨R, slope, hc⟩

end Curve
end EfficientFFA.EllipticCurve
