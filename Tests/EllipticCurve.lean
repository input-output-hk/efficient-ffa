import EfficientFFA

namespace EfficientFFA.Tests.EC
open EllipticCurve

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- A concrete smooth curve with both order-two and order-three points.
def C : Curve (ZMod 7) where
  a := 0
  b := 1
  smooth := by decide

def P : Coordinates (ZMod 7) := ⟨0, 1⟩
def Q : Coordinates (ZMod 7) := ⟨1, 3⟩
def T : Coordinates (ZMod 7) := ⟨3, 0⟩
def D : Coordinates (ZMod 7) := ⟨0, 6⟩

theorem onP : C.OnCurve P := by unfold Curve.OnCurve; decide
theorem onQ : C.OnCurve Q := by unfold Curve.OnCurve; decide
theorem onT : C.OnCurve T := by unfold Curve.OnCurve; decide

example : AddChecks P Q T 2 := by constructor <;> decide
example : ∃ hT : C.OnCurve T, C.point T hT = C.point P onP + C.point Q onQ :=
  C.addition_sound (slope := 2) onP onQ (by decide) (by constructor <;> decide)

-- Doubling an order-three point has the same x-coordinate as its input.
example : P.x = D.x ∧ DoubleChecks C P D 0 := by
  refine ⟨rfl, ?_⟩
  constructor <;> decide

example : ∃ hD : C.OnCurve D, C.point D hD = C.point P onP + C.point P onP :=
  C.doubling_sound (slope := 0) onP (by constructor <;> decide)

theorem three_torsion : 3 • C.point P onP = 0 := by
  obtain ⟨hD, he⟩ := C.doubling_sound onP (R := D) (slope := 0) (by constructor <;> decide)
  have hneg : C.point D hD = -C.point P onP := by
    simp only [Curve.point, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rfl
    · change (6 : ZMod 7) = -1
      decide
  calc
    3 • C.point P onP = (C.point P onP + C.point P onP) + C.point P onP := by
      simp [succ_nsmul, add_assoc]
    _ = 0 := by rw [← he, hneg, neg_add_cancel]

-- The nonidentity order-two point doubles to infinity, but Figure 1 rejects it.
example : C.point T onT + C.point T onT = 0 :=
  (C.double_eq_zero_iff onT).mpr (by decide)
example : ¬ ∃ R slope, DoubleChecks C T R slope := by
  rw [C.doubling_witnesses_iff onT]
  decide

-- If the incomplete-add input x-inequality is omitted, the constraints can accept
-- an off-curve output when both inputs are the same point.
def bad : Coordinates (ZMod 7) := ⟨1, 5⟩
example : AddChecks P P bad 1 ∧ ¬ C.OnCurve bad := by
  constructor
  · constructor <;> decide
  · unfold Curve.OnCurve
    decide

def infA : Encoded (ZMod 7) := ⟨⟨0, 0⟩, true⟩
def infB : Encoded (ZMod 7) := ⟨⟨1, 1⟩, true⟩
def finiteT : Encoded (ZMod 7) := ⟨T, false⟩

theorem validA : C.Valid infA := by intro h; cases h
theorem validB : C.Valid infB := by intro h; cases h
theorem validT : C.Valid finiteT := fun _ => onT

-- Distinct coordinate encodings denote the same identity point.
example : C.decode infA validA = C.decode infB validB := by
  rw [C.decode_infinity validA rfl, C.decode_infinity validB rfl]

-- The two literal Figure 3 identity-copy implications have no output for this pair.
example : ¬ ∃ R, IdentityCopies infA infB R := by
  rw [identity_copies_iff rfl rfl]
  decide

-- Ordered complete addition handles the pair by choosing the left identity branch.
example : C.CompleteAccepts infA infB infB := .left rfl rfl
example : ∃ hR : C.Valid infB,
    C.decode infB hR = C.decode infA validA + C.decode infB validB :=
  C.complete_sound validA validB (.left rfl rfl)

-- The inverse branch also handles finite order-two inputs, without using Figure 1.
example : C.CompleteAccepts finiteT finiteT infA :=
  .inverse rfl rfl rfl (by decide) rfl
example : ∃ hR : C.Valid infA,
    C.decode infA hR = C.decode finiteT validT + C.decode finiteT validT :=
  C.complete_sound validT validT (.inverse rfl rfl rfl (by decide) rfl)

example : C.DoubleAccepts infA infB 3 := by
  refine ⟨rfl, ?_⟩
  intro h
  cases h

end EfficientFFA.Tests.EC

-- Trust audit for every EC library theorem.
#print axioms EfficientFFA.EllipticCurve.Curve.equation_iff
#print axioms EfficientFFA.EllipticCurve.Curve.nonsingular
#print axioms EfficientFFA.EllipticCurve.Curve.point_ne_zero
#print axioms EfficientFFA.EllipticCurve.Curve.point_injective
#print axioms EfficientFFA.EllipticCurve.Curve.same_x_cases
#print axioms EfficientFFA.EllipticCurve.output_determined
#print axioms EfficientFFA.EllipticCurve.add_checks_iff
#print axioms EfficientFFA.EllipticCurve.double_checks_iff
#print axioms EfficientFFA.EllipticCurve.Curve.result_x
#print axioms EfficientFFA.EllipticCurve.Curve.result_y
#print axioms EfficientFFA.EllipticCurve.Curve.slope_chord
#print axioms EfficientFFA.EllipticCurve.Curve.y_ne_neg_of_den
#print axioms EfficientFFA.EllipticCurve.Curve.slope_tangent
#print axioms EfficientFFA.EllipticCurve.Curve.result_group
#print axioms EfficientFFA.EllipticCurve.Curve.addition_sound
#print axioms EfficientFFA.EllipticCurve.Curve.addition_complete
#print axioms EfficientFFA.EllipticCurve.Curve.double_den_ne
#print axioms EfficientFFA.EllipticCurve.Curve.doubling_sound
#print axioms EfficientFFA.EllipticCurve.Curve.doubling_complete
#print axioms EfficientFFA.EllipticCurve.Curve.doubling_witnesses_iff
#print axioms EfficientFFA.EllipticCurve.Curve.decode_finite
#print axioms EfficientFFA.EllipticCurve.Curve.decode_infinity
#print axioms EfficientFFA.EllipticCurve.Curve.flagged_double_sound
#print axioms EfficientFFA.EllipticCurve.Curve.flagged_double_complete
#print axioms EfficientFFA.EllipticCurve.Curve.flagged_double_witnesses_iff
#print axioms EfficientFFA.EllipticCurve.Curve.incomplete_sound
#print axioms EfficientFFA.EllipticCurve.Curve.incomplete_complete
#print axioms EfficientFFA.EllipticCurve.Curve.double_eq_zero_iff
#print axioms EfficientFFA.EllipticCurve.Curve.flagged_double_complete_of_no_two_torsion
#print axioms EfficientFFA.EllipticCurve.identity_copies_iff
#print axioms EfficientFFA.EllipticCurve.Curve.complete_sound
#print axioms EfficientFFA.EllipticCurve.Curve.complete_exists
#print axioms EfficientFFA.EllipticCurve.Curve.complete_correct
