import EfficientFFA.Arithmetic

/-!
# Integer limbs and the multiplication residual

The representation is a finite vector of integers. Bounds are separate
predicates, so the same representation can later express the signed and
unreduced limbs of Section 3.2. No word or array axioms are introduced.
-/

namespace EfficientFFA

abbrev Limbs (n : ℕ) := Fin n → ℤ

/-- Little-endian evaluation, valid for any integer radix. -/
def eval {n : ℕ} (B : ℤ) (x : Limbs n) : ℤ :=
  ∑ i, B ^ i.val * x i

/-- Well-formed limbs, as required by the multiplication theorems. -/
def WellFormed {n : ℕ} (B : ℤ) (x : Limbs n) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i < B

/-- Reduced coefficients in equation (1) of the paper. -/
def mulResidual {n : ℕ} (B q : ℤ) (x y z : Limbs n) : ℤ :=
  (∑ i, ∑ j, (B ^ (i.val + j.val) % q) * x i * y j) -
    ∑ i, (B ^ i.val % q) * z i

/-- Expanding the product of two limb representations. -/
theorem eval_mul {n : ℕ} (B : ℤ) (x y : Limbs n) :
    eval B x * eval B y = ∑ i, ∑ j, B ^ (i.val + j.val) * x i * y j := by
  unfold eval
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- Coefficient reduction preserves the multiplication equation modulo q. -/
theorem mulResidual_mod {n : ℕ} (B q : ℤ) (x y z : Limbs n) :
    mulResidual B q x y z % q = (eval B x * eval B y - eval B z) % q := by
  rw [eval_mul]
  simp [mulResidual, eval, Int.sub_emod, Int.mul_emod, Finset.sum_int_mod]

/-- Algebraic content of equation (1): a quotient witness is exactly what
is needed to express a correct multiplication modulo q. -/
theorem mulResidual_dvd_iff {n : ℕ} (B q : ℤ) (x y z : Limbs n) :
    q ∣ mulResidual B q x y z ↔ eval B x * eval B y ≡ eval B z [ZMOD q] := by
  rw [Int.dvd_iff_emod_eq_zero, mulResidual_mod, Int.ModEq,
    Int.emod_eq_emod_iff_emod_sub_eq_zero]

theorem multiplication_iff_quotient {n : ℕ} (B q : ℤ) (x y z : Limbs n) :
    eval B x * eval B y ≡ eval B z [ZMOD q] ↔
      ∃ k : ℤ, mulResidual B q x y z = k * q := by
  rw [← mulResidual_dvd_iff, dvd_iff_exists_eq_mul_left]

/-- Reconstruction from the native and auxiliary congruences, once bounds
on the equation-(2) residual have been established. This is a core lemma,
not yet the full soundness theorem for the paper's encoded auxiliary checks. -/
theorem multiplication_of_bounded_residual_checks {n : ℕ} (B q k : ℤ)
    (ms : List ℤ) (x y z : Limbs n)
    (hchecks : ∀ m ∈ ms, mulResidual B q x y z - k*q ≡ 0 [ZMOD m])
    (hlo : -moduliLCM ms < mulResidual B q x y z - k*q)
    (hhi : mulResidual B q x y z - k*q < moduliLCM ms) :
    eval B x * eval B y ≡ eval B z [ZMOD q] := by
  apply (multiplication_iff_quotient B q x y z).mpr
  exact ⟨k, sub_eq_zero.mp (eq_zero_of_congruences_of_bounds hchecks hlo hhi)⟩

/-- Linearity over the integers; no assumption of bounded limbs is needed. -/
theorem eval_add {n : ℕ} (B : ℤ) (x y : Limbs n) :
    eval B (fun i => x i + y i) = eval B x + eval B y := by
  simp [eval, mul_add, Finset.sum_add_distrib]

theorem eval_sub {n : ℕ} (B : ℤ) (x y : Limbs n) :
    eval B (fun i => x i - y i) = eval B x - eval B y := by
  simp [eval, mul_sub, Finset.sum_sub_distrib]

theorem eval_scale {n : ℕ} (B c : ℤ) (x : Limbs n) :
    eval B (fun i => c * x i) = c * eval B x := by
  simp [eval, Finset.mul_sum, mul_left_comm]

end EfficientFFA
