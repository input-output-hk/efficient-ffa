import Mathlib

namespace EfficientFFA.EllipticCurve

/-- The short Weierstrass model used by the paper. -/
def model {K : Type*} [Field K] (a b : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, a, b⟩

/-- Smoothness is a checked numerical property of the curve, not a project axiom. -/
structure Curve (K : Type*) [Field K] where
  a : K
  b : K
  smooth : (model a b).Δ ≠ 0

structure Coordinates (K : Type*) where
  x : K
  y : K
  deriving DecidableEq

namespace Curve
variable {K : Type*} [Field K] (C : Curve K)

abbrev W : WeierstrassCurve.Affine K := model C.a C.b
abbrev Point := C.W.Point

def OnCurve (P : Coordinates K) : Prop := P.y^2 = P.x^3 + C.a*P.x + C.b

theorem equation_iff (P : Coordinates K) : C.W.Equation P.x P.y ↔ C.OnCurve P := by
  simp [WeierstrassCurve.Affine.equation_iff, W, model, OnCurve]

theorem nonsingular {P : Coordinates K} (h : C.OnCurve P) : C.W.Nonsingular P.x P.y :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero C.smooth).mp
    ((C.equation_iff P).mpr h)

def point (P : Coordinates K) (h : C.OnCurve P) : C.Point :=
  .some P.x P.y (C.nonsingular h)

theorem point_ne_zero {P : Coordinates K} (h : C.OnCurve P) : C.point P h ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

theorem point_injective {P Q : Coordinates K} {hP : C.OnCurve P} {hQ : C.OnCurve Q}
    (h : C.point P hP = C.point Q hQ) : P = Q := by
  have he : P.x = Q.x ∧ P.y = Q.y := by
    simpa only [point, WeierstrassCurve.Affine.Point.some.injEq] using h
  cases P; cases Q
  simp_all

/-- Equal x-coordinates of curve points imply equal or opposite y-coordinates. -/
theorem same_x_cases {P Q : Coordinates K} (hP : C.OnCurve P) (hQ : C.OnCurve Q)
    (hx : P.x = Q.x) : P.y = Q.y ∨ P.y = -Q.y := by
  simpa [W, model, WeierstrassCurve.Affine.negY] using
    WeierstrassCurve.Affine.Y_eq_of_X_eq ((C.equation_iff P).mpr hP)
      ((C.equation_iff Q).mpr hQ) hx

end Curve

/-- Coordinates fixed by the last two equations in Figures 1 and 2. -/
def result {K : Type*} [Field K] (P Q : Coordinates K) (slope : K) : Coordinates K :=
  ⟨slope^2-P.x-Q.x, slope*(P.x-(slope^2-P.x-Q.x))-P.y⟩

def chord {K : Type*} [Field K] (P Q : Coordinates K) : K := (Q.y-P.y)/(Q.x-P.x)
def tangent {K : Type*} [Field K] (C : Curve K) (P : Coordinates K) : K :=
  (3*P.x^2+C.a)/(2*P.y)

structure AddChecks {K : Type*} [Field K] (P Q R : Coordinates K) (slope : K) : Prop where
  slope_eq : Q.y-P.y-slope*(Q.x-P.x) = 0
  x_eq : P.x+Q.x+R.x-slope^2 = 0
  y_eq : -R.y-P.y-slope*(R.x-P.x) = 0

structure DoubleChecks {K : Type*} [Field K] (C : Curve K)
    (P R : Coordinates K) (slope : K) : Prop where
  slope_eq : 3*P.x^2+C.a-2*P.y*slope = 0
  x_eq : P.x+P.x+R.x-slope^2 = 0
  y_eq : -R.y-P.y-slope*(R.x-P.x) = 0

/-- Solving for the output never divides by x(R)-x(P). -/
theorem output_determined {K : Type*} [Field K] {P Q R : Coordinates K} {slope : K}
    (hx : P.x+Q.x+R.x-slope^2 = 0)
    (hy : -R.y-P.y-slope*(R.x-P.x) = 0) : R = result P Q slope := by
  have hRx : R.x = slope^2-P.x-Q.x := by linear_combination hx
  have hRy : R.y = slope*(P.x-(slope^2-P.x-Q.x))-P.y := by
    rw [← hRx]
    linear_combination -hy
  cases R
  simp_all [result]

theorem add_checks_iff {K : Type*} [Field K] {P Q R : Coordinates K} {slope : K}
    (hne : P.x ≠ Q.x) :
    AddChecks P Q R slope ↔ slope = chord P Q ∧ R = result P Q slope := by
  constructor
  · intro h
    refine ⟨?_, output_determined h.x_eq h.y_eq⟩
    apply (eq_div_iff (sub_ne_zero.mpr hne.symm)).mpr
    linear_combination -h.slope_eq
  · rintro ⟨rfl, rfl⟩
    constructor
    · have hd := div_mul_cancel₀ (Q.y-P.y) (sub_ne_zero.mpr hne.symm)
      dsimp [chord]
      linear_combination -hd
    · dsimp [result]; ring
    · dsimp [result]; ring

theorem double_checks_iff {K : Type*} [Field K] {C : Curve K}
    {P R : Coordinates K} {slope : K} (hden : 2*P.y ≠ 0) :
    DoubleChecks C P R slope ↔ slope = tangent C P ∧ R = result P P slope := by
  constructor
  · intro h
    refine ⟨?_, output_determined h.x_eq h.y_eq⟩
    apply (eq_div_iff hden).mpr
    linear_combination -h.slope_eq
  · rintro ⟨rfl, rfl⟩
    constructor
    · have hd := div_mul_cancel₀ (3*P.x^2+C.a) hden
      dsimp [tangent]
      linear_combination -hd
    · dsimp [result]; ring
    · dsimp [result]; ring

end EfficientFFA.EllipticCurve
