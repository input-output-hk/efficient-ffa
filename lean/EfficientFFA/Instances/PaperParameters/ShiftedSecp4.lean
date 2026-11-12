import EfficientFFA.Instances.PaperParameters.Secp4
import EfficientFFA.ShiftedEncoding.EllipticCurve

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace EfficientFFA.Instances.PaperParameters.secp4

/-- Recheck the shifted polynomials: the existing widths happen to suffice,
but this conclusion does not follow from ordinary ec_valid. -/
theorem shifted_valid (f : NativeField) (k : Native.GateKind) :
    (ec f).Valid ((k.expression 0 7).compileShifted (ec f).B 4) := by
  cases f <;> cases k <;> constructor <;> constructor <;> decide

/-- This production radix also satisfies the separate unique-zero condition. -/
theorem unique_zero_capacity (f : NativeField) : (ec f).B^4 < 2*(ec f).q := by
  cases f <;> decide

def shiftedEncoding (f : NativeField) {q : ℕ} [Fact q.Prime]
    (C : EllipticCurve.Curve (ZMod q)) (hq : (ec f).q = q)
    (ha : C.a.val = 0) (hb : C.b.val = 7) : Native.ShiftedECEncoding C 4 1 where
  params := ec f
  foreign_eq := hq
  capacity := capacity f
  valid k := by simpa [ha, hb] using shifted_valid f k

end EfficientFFA.Instances.PaperParameters.secp4
