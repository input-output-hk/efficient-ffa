import EfficientFFA.LazyArithmetic
import EfficientFFA.Multiplication.Bounds

/-! # Normalization constraints for eq:normalization
These definitions are the auxiliary equations, widths and no-wrap conditions
of app:normalization, with the paper's uniform signed input bound. -/

namespace EfficientFFA.Normalization

/-- Coefficient-reduced linear residual from eq:normalization. -/
def residual {n : ℕ} (B q : ℤ) (x z : Limbs n) : ℤ :=
  (∑ i, (B ^ i.val % q) * x i) - ∑ i, (B ^ i.val % q) * z i

theorem residual_mod {n : ℕ} (B q : ℤ) (x z : Limbs n) :
    residual B q x z % q = (eval B x - eval B z) % q := by
  simp [residual, eval, Int.sub_emod, Int.mul_emod, Finset.sum_int_mod]

theorem residual_dvd_iff {n : ℕ} (B q : ℤ) (x z : Limbs n) :
    q ∣ residual B q x z ↔ eval B x ≡ eval B z [ZMOD q] := by
  rw [Int.dvd_iff_emod_eq_zero, residual_mod, Int.ModEq,
    Int.emod_eq_emod_iff_emod_sub_eq_zero]

theorem normalization_iff_quotient {n : ℕ} (B q : ℤ) (x z : Limbs n) :
    eval B x ≡ eval B z [ZMOD q] ↔ ∃ k : ℤ, residual B q x z = k * q := by
  rw [← residual_dvd_iff, dvd_iff_exists_eq_mul_left]

structure Parameters (n r : ℕ) where
  limit : ℤ
  B : ℤ
  q : ℤ
  p : ℤ
  M : Fin r → ℤ
  t : ℕ
  tm : Fin r → ℕ

namespace Parameters
variable {n r : ℕ}

def singleCoeff (P : Parameters n r) (i : Fin n) : ℤ := P.B ^ i.val % P.q
def InputBounded (P : Parameters n r) (x : Limbs n) : Prop :=
  LazyArithmetic.Bounded (fun _ => -P.limit) (fun _ => P.limit) x

def A (P : Parameters n r) : ℤ := (P.limit + P.B) * ∑ i, P.singleCoeff i
def C (P : Parameters n r) : ℤ := P.limit * ∑ i, P.singleCoeff i
/-- Ceiling of -A/q for positive q: negate after integer division. -/
def kmin (P : Parameters n r) : ℤ := -(P.A / P.q)
def kmax (P : Parameters n r) : ℤ := P.C / P.q
def Umax (P : Parameters n r) : ℤ := 2 ^ P.t
def Vmax (P : Parameters n r) (a : Fin r) : ℤ := 2 ^ P.tm a

def Am (P : Parameters n r) (a : Fin r) : ℤ :=
  (P.limit + P.B) * (∑ i, P.singleCoeff i % P.M a) +
    P.Umax * (P.q % P.M a) + (P.kmin * P.q) % P.M a

def Cm (P : Parameters n r) (a : Fin r) : ℤ :=
  P.limit * (∑ i, P.singleCoeff i % P.M a) -
    (P.kmin * P.q) % P.M a

def lmin (P : Parameters n r) (a : Fin r) : ℤ := -(P.Am a / P.M a)
def lmax (P : Parameters n r) (a : Fin r) : ℤ := P.Cm a / P.M a

def nativeResidual (P : Parameters n r) (x z : Limbs n) (u : ℤ) : ℤ :=
  residual P.B P.q x z - (u + P.kmin) * P.q

/-- Auxiliary expression before subtracting its quotient times the modulus. -/
def auxCore (P : Parameters n r) (x z : Limbs n) (u : ℤ) (a : Fin r) : ℤ :=
  (∑ i, (P.singleCoeff i % P.M a) * x i) -
    (∑ i, (P.singleCoeff i % P.M a) * z i) -
    u * (P.q % P.M a) - (P.kmin * P.q) % P.M a

def auxResidual (P : Parameters n r) (x z : Limbs n)
    (u v : ℤ) (a : Fin r) : ℤ :=
  P.auxCore x z u a - (v + P.lmin a) * P.M a

def auxLower (P : Parameters n r) (a : Fin r) : ℤ :=
  -P.Am a - (P.Vmax a + P.lmin a) * P.M a

def auxUpper (P : Parameters n r) (a : Fin r) : ℤ :=
  P.Cm a - P.lmin a * P.M a

def moduli (P : Parameters n r) : List ℤ := P.p :: List.ofFn P.M

def L (P : Parameters n r) : ℤ := moduliLCM P.moduli

structure Positive (P : Parameters n r) : Prop where
  limit_nonneg : 0 ≤ P.limit
  radix : 0 < P.B
  foreign : 0 < P.q
  native : 0 < P.p
  auxiliary : ∀ a, 0 < P.M a

structure WidthBounds (P : Parameters n r) : Prop where
  native : P.kmax - P.kmin < P.Umax
  auxiliary : ∀ a, P.lmax a - P.lmin a < P.Vmax a

structure NoWrap (P : Parameters n r) : Prop where
  auxiliary_lower : ∀ a, -P.p < P.auxLower a
  auxiliary_upper : ∀ a, P.auxUpper a < P.p
  reconstruction_lower : P.A + (P.Umax + P.kmin) * P.q < P.L
  reconstruction_upper : P.C - P.kmin * P.q < P.L

structure Valid (P : Parameters n r) : Prop where
  positive : P.Positive
  widths : P.WidthBounds
  nowrap : P.NoWrap

/-- The actual equations are checked modulo the native modulus p. Signed input bounds and
output well-formedness are explicit premises of the endpoint theorems. -/
structure Accepts (P : Parameters n r) (x z : Limbs n)
    (u : ℤ) (v : Fin r → ℤ) : Prop where
  u_range : 0 ≤ u ∧ u < P.Umax
  v_range : ∀ a, 0 ≤ v a ∧ v a < P.Vmax a
  native : P.nativeResidual x z u ≡ 0 [ZMOD P.p]
  auxiliary : ∀ a, P.auxResidual x z u (v a) a ≡ 0 [ZMOD P.p]

end Parameters
end EfficientFFA.Normalization
