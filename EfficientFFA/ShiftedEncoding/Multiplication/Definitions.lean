import EfficientFFA.ShiftedEncoding.Representation
import EfficientFFA.Multiplication.Bounds

/-! # Shifted multiplication constraints
The extra linear terms in Section 3.2.4 require new upper bounds. Quotient
witnesses and auxiliary checks use these bounds, not the unshifted ones. -/

namespace EfficientFFA.ShiftedEncoding.Multiplication

/-- The shifted multiplication identity with coefficients reduced modulo q. -/
def residual {n : ℕ} (B q : ℤ) (x y z : Limbs n) : ℤ :=
  (∑ i, ∑ j, (B ^ (i.val+j.val) % q) * x i * y j) +
    (∑ i, (B ^ i.val % q) * x i) + (∑ i, (B ^ i.val % q) * y i) -
    ∑ i, (B ^ i.val % q) * z i

theorem shifted_product_identity {n : ℕ} (B : ℤ) (x y z : Limbs n) :
    value B x * value B y - value B z =
      eval B x * eval B y + eval B x + eval B y - eval B z := by
  unfold value
  ring

theorem residual_mod {n : ℕ} (B q : ℤ) (x y z : Limbs n) :
    residual B q x y z % q = (value B x * value B y - value B z) % q := by
  rw [shifted_product_identity, eval_mul]
  simp [residual, eval, Int.add_emod, Int.sub_emod, Int.mul_emod, Finset.sum_int_mod]

theorem residual_dvd_iff {n : ℕ} (B q : ℤ) (x y z : Limbs n) :
    q ∣ residual B q x y z ↔ value B x * value B y ≡ value B z [ZMOD q] := by
  rw [Int.dvd_iff_emod_eq_zero, residual_mod, Int.ModEq,
    Int.emod_eq_emod_iff_emod_sub_eq_zero]

theorem multiplication_iff_quotient {n : ℕ} (B q : ℤ) (x y z : Limbs n) :
    value B x * value B y ≡ value B z [ZMOD q] ↔
      ∃ k : ℤ, residual B q x y z = k * q := by
  rw [← residual_dvd_iff, dvd_iff_exists_eq_mul_left]

structure Parameters (n r : ℕ) where
  B : ℤ
  q : ℤ
  p : ℤ
  M : Fin r → ℤ
  t : ℕ
  tm : Fin r → ℕ

namespace Parameters
variable {n r : ℕ}

def singleCoeff (P : Parameters n r) (i : Fin n) : ℤ := P.B ^ i.val % P.q
def doubleCoeff (P : Parameters n r) (i j : Fin n) : ℤ :=
  P.B ^ (i.val + j.val) % P.q

def A (P : Parameters n r) : ℤ := (P.B-1) * ∑ i, P.singleCoeff i
def C (P : Parameters n r) : ℤ :=
  (P.B-1)^2 * (∑ i, ∑ j, P.doubleCoeff i j) + 2 * P.A
/-- Ceiling of -A/q for positive q: negate after integer division. -/
def kmin (P : Parameters n r) : ℤ := -(P.A / P.q)
def kmax (P : Parameters n r) : ℤ := P.C / P.q
def Umax (P : Parameters n r) : ℤ := 2 ^ P.t
def Vmax (P : Parameters n r) (a : Fin r) : ℤ := 2 ^ P.tm a

def Am (P : Parameters n r) (a : Fin r) : ℤ :=
  (P.B-1) * (∑ i, P.singleCoeff i % P.M a) +
    P.Umax * (P.q % P.M a) + (P.kmin * P.q) % P.M a

def Cm (P : Parameters n r) (a : Fin r) : ℤ :=
  (P.B-1)^2 * (∑ i, ∑ j, P.doubleCoeff i j % P.M a) +
    2 * (P.B-1) * (∑ i, P.singleCoeff i % P.M a) -
    (P.kmin * P.q) % P.M a

def lmin (P : Parameters n r) (a : Fin r) : ℤ := -(P.Am a / P.M a)
def lmax (P : Parameters n r) (a : Fin r) : ℤ := P.Cm a / P.M a

def nativeResidual (P : Parameters n r) (x y z : Limbs n) (u : ℤ) : ℤ :=
  residual P.B P.q x y z - (u + P.kmin) * P.q

/-- Auxiliary expression before subtracting its quotient times the modulus. -/
def auxCore (P : Parameters n r) (x y z : Limbs n) (u : ℤ) (a : Fin r) : ℤ :=
  (∑ i, ∑ j, (P.doubleCoeff i j % P.M a) * x i * y j) +
    (∑ i, (P.singleCoeff i % P.M a) * x i) +
    (∑ i, (P.singleCoeff i % P.M a) * y i) -
    (∑ i, (P.singleCoeff i % P.M a) * z i) -
    u * (P.q % P.M a) - (P.kmin * P.q) % P.M a

def auxResidual (P : Parameters n r) (x y z : Limbs n)
    (u v : ℤ) (a : Fin r) : ℤ :=
  P.auxCore x y z u a - (v + P.lmin a) * P.M a

def auxLower (P : Parameters n r) (a : Fin r) : ℤ :=
  -P.Am a - (P.Vmax a + P.lmin a) * P.M a

def auxUpper (P : Parameters n r) (a : Fin r) : ℤ :=
  P.Cm a - P.lmin a * P.M a

def moduli (P : Parameters n r) : List ℤ := P.p :: List.ofFn P.M

def L (P : Parameters n r) : ℤ := moduliLCM P.moduli

structure Positive (P : Parameters n r) : Prop where
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

/-- The actual equations are checked modulo the native modulus p. Limb
well-formedness is an explicit input premise of the endpoint theorems. -/
structure Accepts (P : Parameters n r) (x y z : Limbs n)
    (u : ℤ) (v : Fin r → ℤ) : Prop where
  u_range : 0 ≤ u ∧ u < P.Umax
  v_range : ∀ a, 0 ≤ v a ∧ v a < P.Vmax a
  native : P.nativeResidual x y z u ≡ 0 [ZMOD P.p]
  auxiliary : ∀ a, P.auxResidual x y z u (v a) a ≡ 0 [ZMOD P.p]

end Parameters
end EfficientFFA.ShiftedEncoding.Multiplication
