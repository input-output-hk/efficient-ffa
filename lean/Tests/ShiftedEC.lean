import EfficientFFA.Instances.ShiftedCurve17

namespace EfficientFFA.Tests.ShiftedEC
open Native EllipticCurve Instances.ShiftedCurve17

/-- All-zero limbs encode one; [1,3] encodes zero. This catches an accidental
reuse of ordinary limb interpretation in the new compiler. -/
example : ShiftedEncoding.value 5 (![0,0] : Limbs 2) = 1 := by decide
example : ShiftedEncoding.value 5 (![1,3] : Limbs 2) = 17 := by decide

/-- The slope equation for (5,1)+(6,3) uses slope 2. Check actual supplied limbs
and explicit quotient witnesses, not only existence over semantic coordinates. -/
def wires : Fin 8 × Fin 2 → ℤ :=
  fun a => (![![4,0], ![0,0], ![0,1], ![2,0], ![4,1], ![0,1], ![1,0], ![1,3]]) a.1 a.2

def slopePoly := (GateKind.slopePlus.expression 2 2).compileShifted 5 2

theorem shifted_slope_accepts : params.Accepts slopePoly wires
    (params.witnessU slopePoly wires) (params.witnessV slopePoly wires) := by
  apply Expression.shifted_witnesses_accept params (valid .slopePlus).positive
    (GateKind.slopePlus.expression 2 2) (valid .slopePlus).widths
  · rintro ⟨a, i⟩; fin_cases a <;> fin_cases i <;> decide
  · decide

/-- Forgetting the +1 shift makes these same supplied wires fail the slope identity. -/
example : ¬ Native.Polynomial.eval ((GateKind.slopePlus.expression 2 2).compile 5 2) wires ≡
    0 [ZMOD 17] := by decide

example : encoding.Add (⟨5,1⟩ : Coordinates (ZMod 17)) ⟨6,3⟩ ⟨10,6⟩ 2 := by
  apply (encoding.add_iff _ _ _ _).mpr
  constructor <;> decide

example : encoding.Double (⟨5,1⟩ : Coordinates (ZMod 17)) ⟨6,3⟩ 13 := by
  apply (encoding.double_iff _ _ _).mpr
  constructor <;> decide

end EfficientFFA.Tests.ShiftedEC
