import EfficientFFA

namespace EfficientFFA.Tests

-- Noncoprime and signed moduli: no product-of-moduli shortcut.
example : moduliLCM [4, 6] = 12 := by norm_num [moduliLCM, Int.lcm]
example : moduliLCM [-4, 6] = 12 := by norm_num [moduliLCM, Int.lcm]
example : moduliLCM [] = 1 := rfl
example : moduliLCM [6, 0] = 0 := by norm_num [moduliLCM, Int.lcm]
example : (4 : ℤ) ∣ 12 ∧ (6 : ℤ) ∣ 12 ∧ ¬ (24 : ℤ) ∣ 12 := by norm_num

-- The endpoints in the reconstruction theorem cannot be made non-strict.
example : (6 : ℤ) ≡ 0 [ZMOD 6] ∧ -(6 : ℤ) ≤ 6 ∧ (6 : ℤ) ≤ 6 ∧ (6 : ℤ) ≠ 0 := by
  norm_num [Int.ModEq]

-- A non-power-of-two radix and little-endian limbs: 12 * 23 = 3 (mod 7).
def x : Limbs 2 := ![2, 1]
def y : Limbs 2 := ![3, 2]
def z : Limbs 2 := ![3, 0]

example : WellFormed 10 x := by
  intro i
  fin_cases i <;> norm_num [x]

example : eval 10 x = 12 ∧ eval 10 y = 23 ∧ eval 10 z = 3 := by
  norm_num [eval, x, y, z, Fin.sum_univ_two]

example : mulResidual 10 7 x y z = 4 * 7 := by
  norm_num [mulResidual, x, y, z, Fin.sum_univ_two]

example : eval 10 x * eval 10 y ≡ eval 10 z [ZMOD 7] := by
  apply (multiplication_iff_quotient 10 7 x y z).mpr
  exact ⟨4, by norm_num [mulResidual, x, y, z, Fin.sum_univ_two]⟩

-- Signed limbs have ordinary integer meaning; they are not machine words.
example : eval 10 (![(-1), 2] : Limbs 2) = 19 := by
  norm_num [eval, Fin.sum_univ_two]

-- Concrete use of reconstruction; this is a lemma-level example, not a
-- parameter instance of the full encoded FFA constraint system.
example : eval 10 x * eval 10 y ≡ eval 10 z [ZMOD 7] := by
  apply multiplication_of_bounded_residual_checks 10 7 4 [5, 6] x y z
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;>
      norm_num [mulResidual, x, y, z, Fin.sum_univ_two, Int.ModEq]
  · norm_num [mulResidual, x, y, z, Fin.sum_univ_two, moduliLCM, Int.lcm]
  · norm_num [mulResidual, x, y, z, Fin.sum_univ_two, moduliLCM, Int.lcm]

end EfficientFFA.Tests

#print axioms EfficientFFA.congruent_all_iff_lcm
#print axioms EfficientFFA.eq_zero_of_modEq_of_bounds
#print axioms EfficientFFA.eq_zero_of_congruences_of_bounds
#print axioms EfficientFFA.eval_mul
#print axioms EfficientFFA.mulResidual_mod
#print axioms EfficientFFA.mulResidual_dvd_iff
#print axioms EfficientFFA.multiplication_iff_quotient
#print axioms EfficientFFA.multiplication_of_bounded_residual_checks
#print axioms EfficientFFA.eval_add
#print axioms EfficientFFA.eval_sub
#print axioms EfficientFFA.eval_scale
