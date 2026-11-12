import EfficientFFA.ShiftedEncoding.EllipticCurve
import EfficientFFA.Instances.Curve17

namespace EfficientFFA.Instances.ShiftedCurve17
open Native

/-- Two radix-5 shifted limbs, with independently checked shifted widths. -/
def params : Parameters 1 where
  B := 5
  q := 17
  p := 65537
  M := fun _ => 101
  t := 8
  tm := fun _ => 8

theorem valid (k : GateKind) :
    params.Valid ((k.expression 2 2).compileShifted 5 2) := by
  cases k <;> constructor <;> constructor <;> decide

def encoding : ShiftedECEncoding Curve17.curve 2 1 where
  params := params
  foreign_eq := rfl
  capacity := by decide
  valid k := valid k

theorem unique_zero :
    ∃! x : Limbs 2, WellFormed params.B x ∧
      ShiftedEncoding.value params.B x ≡ 0 [ZMOD params.q] :=
  encoding.unique_zero (by decide)

end EfficientFFA.Instances.ShiftedCurve17
