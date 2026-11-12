import EfficientFFA.Instances.PaperParameters.Constants
import EfficientFFA.Paper.Arithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace EfficientFFA.Instances.PaperParameters.secp4

def multiplication (f : NativeField) : Multiplication.Parameters 4 1 where
  B := 2^64
  q := secpQ
  p := f.modulus
  M := fun _ => 2^128
  t := 67
  tm := fun _ => 98

theorem multiplication_valid (f : NativeField) : (multiplication f).Valid := by
  cases f <;> constructor <;> constructor <;> decide

def ec (f : NativeField) : Native.Parameters 1 where
  B := 2^64
  q := secpQ
  p := f.modulus
  M := fun _ => 2^128
  t := 69
  tm := fun _ => 100

/-- One shared choice of widths supports all nine compiled coordinate identities. -/
theorem ec_valid (f : NativeField) (k : Native.GateKind) :
    (ec f).Valid ((k.expression 0 7).compile (ec f).B 4) := by
  cases f <;> cases k <;> constructor <;> constructor <;> decide

theorem capacity (f : NativeField) : (ec f).q ≤ (ec f).B^4 := by
  cases f <;> decide

/-- A certified normalization limit with the SAME radix and auxiliary moduli.
This is a sufficient limit, not a claim of maximality. -/
def normalization (f : NativeField) : Normalization.Parameters 4 1 where
  limit := 2^186
  B := 2^64
  q := secpQ
  p := f.modulus
  M := fun _ => 2^128
  t := 124
  tm := fun _ => 125

theorem normalization_valid (f : NativeField) : (normalization f).Valid := by
  cases f <;> constructor <;> constructor <;> decide

theorem same_moduli (f : NativeField) :
    (normalization f).moduli = (multiplication f).moduli := rfl

/-- The EC identity encoding uses the same auxiliary and native moduli too. -/
theorem ec_same_moduli (f : NativeField) :
    (ec f).p :: List.ofFn (ec f).M = (multiplication f).moduli := rfl

/-- Connect the integer certificates to a curve once the field and coefficients
are supplied. Primality and smoothness are explicit inputs, not numerical claims
proved by this file. -/
def encoding (f : NativeField) {q : ℕ} [Fact q.Prime] (C : EllipticCurve.Curve (ZMod q))
    (hq : (ec f).q = q) (ha : C.a.val = 0) (hb : C.b.val = 7) :
    Native.ECEncoding C 4 1 where
  params := ec f
  foreign_eq := hq
  capacity := capacity f
  valid k := by simpa [ha, hb] using ec_valid f k
  native_gt_one := by cases f <;> decide

/-- Quantitative native headroom for this radix. -/
theorem radix_headroom (f : NativeField) : (ec f).B^2 < (ec f).p := by
  cases f <;> decide

/-- Every signed input bound up to the certified limit admits normalization
with these fixed moduli, shifts and witness widths. -/
theorem normalize (f : NativeField) {L : ℤ} (hL : L ≤ 2^186)
    {x : Limbs 4} (hx : LazyArithmetic.Bounded (fun _ => -L) (fun _ => L) x) :
    ∃ z u v, WellFormed (normalization f).B z ∧
      (normalization f).Accepts x z u v ∧
      eval (normalization f).B z = eval (normalization f).B x % (normalization f).q :=
  Paper.normalization_exists_below_limit (normalization f) (normalization_valid f)
    (capacity f) hL hx

end EfficientFFA.Instances.PaperParameters.secp4
