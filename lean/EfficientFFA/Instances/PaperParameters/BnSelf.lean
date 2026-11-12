import EfficientFFA.Instances.PaperParameters.Constants
import EfficientFFA.Paper.Arithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace EfficientFFA.Instances.PaperParameters.bnSelf

def multiplication : Multiplication.Parameters 6 1 where
  B := 2^52
  q := bnQ
  p := bnP
  M := fun _ => 2^142
  t := 108
  tm := fun _ => 108

theorem multiplication_valid : (multiplication).Valid := by
  constructor <;> constructor <;> decide

def ec : Native.Parameters 1 where
  B := 2^52
  q := bnQ
  p := bnP
  M := fun _ => 2^142
  t := 109
  tm := fun _ => 110

/-- One shared choice of widths supports all nine compiled coordinate identities. -/
theorem ec_valid (k : Native.GateKind) :
    (ec).Valid ((k.expression 0 3).compile (ec).B 6) := by
  cases k <;> constructor <;> constructor <;> decide

theorem capacity : (ec).q ≤ (ec).B^6 := by
  decide

/-- A certified normalization limit with the SAME radix and auxiliary moduli.
This is a sufficient limit, not a claim of maximality. -/
def normalization : Normalization.Parameters 6 1 where
  limit := 2^111
  B := 2^52
  q := bnQ
  p := bnP
  M := fun _ => 2^142
  t := 112
  tm := fun _ => 111

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
    (hq : (ec).q = q) (ha : C.a.val = 0) (hb : C.b.val = 3) :
    Native.ECEncoding C 6 1 where
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
theorem normalize {L : ℤ} (hL : L ≤ 2^111)
    {x : Limbs 6} (hx : LazyArithmetic.Bounded (fun _ => -L) (fun _ => L) x) :
    ∃ z u v, WellFormed (normalization).B z ∧
      (normalization).Accepts x z u v ∧
      eval (normalization).B z = eval (normalization).B x % (normalization).q :=
  Paper.normalization_exists_below_limit (normalization) (normalization_valid)
    (capacity) hL hx

end EfficientFFA.Instances.PaperParameters.bnSelf
