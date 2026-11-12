import EfficientFFA.Instances.PaperParameters.Constants
import EfficientFFA.Paper.Arithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace EfficientFFA.Instances.PaperParameters.blsSelf

def multiplication : Multiplication.Parameters 7 2 where
  B := 2^56
  q := blsQ
  p := blsP
  M := ![2^136, 2^136-2]
  t := 115
  tm := ![116, 116]

theorem multiplication_valid : (multiplication).Valid := by
  constructor <;> constructor <;> decide

def ec : Native.Parameters 2 where
  B := 2^56
  q := blsQ
  p := blsP
  M := ![2^136, 2^136-2]
  t := 117
  tm := ![118, 118]

/-- One shared choice of widths supports all nine compiled coordinate identities. -/
theorem ec_valid (k : Native.GateKind) :
    (ec).Valid ((k.expression 0 4).compile (ec).B 7) := by
  cases k <;> constructor <;> constructor <;> decide

theorem capacity : (ec).q ≤ (ec).B^7 := by
  decide

/-- A certified normalization limit with the SAME radix and auxiliary moduli.
This is a sufficient limit, not a claim of maximality. -/
def normalization : Normalization.Parameters 7 2 where
  limit := 2^140
  B := 2^56
  q := blsQ
  p := blsP
  M := ![2^136, 2^136-2]
  t := 97
  tm := ![118, 118]

theorem normalization_valid : (normalization).Valid := by
  constructor <;> constructor <;> decide

theorem same_moduli :
    (normalization).moduli = (multiplication).moduli := rfl

/-- The EC identity encoding uses the same auxiliary and native moduli too. -/
theorem ec_same_moduli :
    (ec).p :: List.ofFn (ec).M = (multiplication).moduli := rfl

/-- Connect the integer certificates to a curve once the field and coefficients
are supplied. Primality and smoothness are explicit inputs, not numerical claims
proved by this file. -/
def encoding {q : ℕ} [Fact q.Prime] (C : EllipticCurve.Curve (ZMod q))
    (hq : (ec).q = q) (ha : C.a.val = 0) (hb : C.b.val = 4) :
    Native.ECEncoding C 7 2 where
  params := ec
  foreign_eq := hq
  capacity := capacity
  valid k := by simpa [ha, hb] using ec_valid k
  native_gt_one := by decide

/-- Quantitative native headroom for this radix. -/
theorem radix_headroom : (ec).B^2 < (ec).p := by
  decide

/-- Every signed input bound up to the certified limit admits normalization
with these fixed moduli, shifts and witness widths. -/
theorem normalize {L : ℤ} (hL : L ≤ 2^140)
    {x : Limbs 7} (hx : LazyArithmetic.Bounded (fun _ => -L) (fun _ => L) x) :
    ∃ z u v, WellFormed (normalization).B z ∧
      (normalization).Accepts x z u v ∧
      eval (normalization).B z = eval (normalization).B x % (normalization).q :=
  Paper.normalization_exists_below_limit (normalization) (normalization_valid)
    (capacity) hL hx

end EfficientFFA.Instances.PaperParameters.blsSelf
