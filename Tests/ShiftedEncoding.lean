import EfficientFFA
import Tests.LazyNormalization

namespace EfficientFFA.Tests.Shifted
open ShiftedEncoding

-- The unique zero is [1,2] in base three: 1 + 1 + 3*2 = 8.
example : ∃! x : Limbs 2, WellFormed 3 x ∧ value 3 x ≡ 0 [ZMOD 8] :=
  exists_unique_zero (by decide) (by decide) (by decide) (by decide)

example (x : Limbs 2) (hx : WellFormed 3 x) :
    value 3 x ≡ 0 [ZMOD 8] ↔ ∀ i, x i = (![1, 2] : Limbs 2) i := by
  exact zero_iff_limbs (by decide) (by decide) hx
    (by intro i; fin_cases i <;> decide) (by decide)

example (x : Limbs 2) (hx : WellFormed 3 x) :
    value 3 x ≡ 0 [ZMOD 8] ↔ ∀ i, x i ≡ (![1, 2] : Limbs 2) i [ZMOD 131] := by
  exact zero_iff_native_checks (by decide) (by decide) (by decide) hx
    (by intro i; fin_cases i <;> decide) (by decide)

-- Only zero is claimed unique: these different bounded vectors both encode one.
example : value 3 (![0, 0] : Limbs 2) ≡ value 3 (![2, 2] : Limbs 2) [ZMOD 8] ∧
    (![0, 0] : Limbs 2) ≠ ![2, 2] := by decide

-- The strict capacity condition is necessary: B^n = 2q admits two zeros.
example : (2 : ℤ)^2 = 2*2 ∧
    value 2 (![1, 0] : Limbs 2) ≡ 0 [ZMOD 2] ∧
    value 2 (![1, 1] : Limbs 2) ≡ 0 [ZMOD 2] ∧
    (![1, 0] : Limbs 2) ≠ ![1, 1] := by decide

-- Without limb bounds, even the same integer expansion need not be unique.
example : eval 3 (![1, 2] : Limbs 2) = eval 3 (![4, 1] : Limbs 2) ∧
    value 3 (![4, 1] : Limbs 2) ≡ 0 [ZMOD 8] ∧
    (![1, 2] : Limbs 2) ≠ ![4, 1] := by decide

-- Native comparisons alone can alias if the radix exceeds the native modulus.
example : (∀ i : Fin 2, (![2, 2] : Limbs 2) i ≡ (![0, 2] : Limbs 2) i [ZMOD 2]) ∧
    value 4 (![0, 2] : Limbs 2) ≡ 0 [ZMOD 9] ∧
    ¬ value 4 (![2, 2] : Limbs 2) ≡ 0 [ZMOD 9] := by decide

-- Corrections are applied only to the least significant limb.
example : add (![0, 0] : Limbs 2) ![0, 0] = ![1, 0] ∧
    sub (![0, 0] : Limbs 2) ![0, 0] = ![-1, 0] ∧
    neg (![0, 0] : Limbs 2) = ![-2, 0] ∧
    scale (-2) (![1, 0] : Limbs 2) = ![-5, 0] := by decide

example {lo hi x : Limbs 2} (hx : LazyArithmetic.Bounded lo hi x) :
    LazyArithmetic.Bounded (bump (-3) (fun i => -2*hi i))
      (bump (-3) (fun i => -2*lo i)) (scale (-2) x) := by
  simpa using bounded_scale (-2) hx

-- Signed subtraction and the unchanged normalization constraints produce shifted zero.
private abbrev N := EfficientFFA.Tests.LazyNormalization.P
example : value N.B (sub (![0, 0] : Limbs 2) ![0, 0]) ≡
    value N.B (![1, 2] : Limbs 2) [ZMOD N.q] := by
  apply stored_normalization_sound N
    EfficientFFA.Tests.LazyNormalization.valid.positive
    EfficientFFA.Tests.LazyNormalization.valid.nowrap
    (stored := ![130, 0]) (u := 3) (v := ![6, 6])
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · constructor <;> decide

-- A full shifted multiplication instance, with revised upper bounds.
def P : ShiftedEncoding.Multiplication.Parameters 2 2 where
  B := 3
  q := 8
  p := 131
  M := ![2, 4]
  t := 3
  tm := ![4, 5]

theorem valid : P.Valid := by
  constructor <;> constructor <;> decide

-- Shifted values 2 * 3 = 6, and explicit quotient witnesses.
example : P.Accepts ![1, 0] ![2, 0] ![2, 1] 1 ![3, 2] := by constructor <;> decide
example : P.witnessU ![1, 0] ![2, 0] ![2, 1] = 1 ∧
    P.witnessV ![1, 0] ![2, 0] ![2, 1] = ![3, 2] := by decide

-- Zero times a maximal representation still gives the unique zero.
example : P.Accepts ![1, 2] ![2, 2] ![1, 2] 5 ![10, 10] := by constructor <;> decide

-- The maximum shifted residual exceeds the old unshifted upper bound of 32.
example : P.C = 48 ∧
    ShiftedEncoding.Multiplication.residual P.B P.q ![2, 2] ![2, 2] ![0, 0] = 48 := by decide
example : P.Accepts ![2, 2] ![2, 2] ![0, 0] 7 ![14, 14] := by constructor <;> decide

-- The old unshifted answer is rejected for every possible witness.
example : ¬ ∃ u v, P.Accepts ![1, 0] ![2, 0] ![2, 0] u v := by
  intro ha
  have hm := (P.accepts_iff_multiplication valid
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide)).mp ha
  norm_num [value, eval, P, Fin.sum_univ_two, Int.ModEq] at hm

example (x y : Limbs 2) (hx : WellFormed P.B x) (hy : WellFormed P.B y) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts x y z u v :=
  P.multiplication_exists valid.positive valid.widths (by decide) hx hy

end EfficientFFA.Tests.Shifted

-- Trust audit for every new library theorem.
#print axioms EfficientFFA.eval_head_tail
#print axioms EfficientFFA.eval_bounds
#print axioms EfficientFFA.eval_injective
#print axioms EfficientFFA.ShiftedEncoding.zero_iff_eval
#print axioms EfficientFFA.ShiftedEncoding.exists_unique_zero
#print axioms EfficientFFA.ShiftedEncoding.zero_iff_limbs
#print axioms EfficientFFA.ShiftedEncoding.exists_representation
#print axioms EfficientFFA.ShiftedEncoding.zero_iff_native_checks
#print axioms EfficientFFA.ShiftedEncoding.eval_bump
#print axioms EfficientFFA.ShiftedEncoding.value_add
#print axioms EfficientFFA.ShiftedEncoding.value_sub
#print axioms EfficientFFA.ShiftedEncoding.value_neg
#print axioms EfficientFFA.ShiftedEncoding.value_add_constant
#print axioms EfficientFFA.ShiftedEncoding.value_scale
#print axioms EfficientFFA.ShiftedEncoding.bounded_bump
#print axioms EfficientFFA.ShiftedEncoding.bounded_add
#print axioms EfficientFFA.ShiftedEncoding.bounded_sub
#print axioms EfficientFFA.ShiftedEncoding.bounded_neg
#print axioms EfficientFFA.ShiftedEncoding.bounded_scale
#print axioms EfficientFFA.ShiftedEncoding.represents_bump
#print axioms EfficientFFA.ShiftedEncoding.represents_add
#print axioms EfficientFFA.ShiftedEncoding.represents_sub
#print axioms EfficientFFA.ShiftedEncoding.represents_neg
#print axioms EfficientFFA.ShiftedEncoding.represents_scale
#print axioms EfficientFFA.ShiftedEncoding.value_congr_iff
#print axioms EfficientFFA.ShiftedEncoding.normalization_iff
#print axioms EfficientFFA.ShiftedEncoding.stored_normalization_sound
#print axioms EfficientFFA.ShiftedEncoding.stored_normalization_exists
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.shifted_product_identity
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.residual_mod
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.residual_dvd_iff
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.multiplication_iff_quotient
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.residual_bounds
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.auxCore_bounds
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.nativeResidual_bounds
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.auxResidual_bounds
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.auxCore_congr
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.multiplication_sound
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.canonical_witnesses_accept
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.multiplication_complete
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.accepts_iff_multiplication
#print axioms EfficientFFA.ShiftedEncoding.Multiplication.Parameters.multiplication_exists
