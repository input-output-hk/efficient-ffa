import EfficientFFA
open scoped ENNReal

namespace EfficientFFA.Tests.MSM
open EfficientFFA.MSM

private def bases : ℕ → ZMod 17 := fun _ => 1
private def digits : ℕ → ℕ → ℕ := fun i _ => if i = 0 then 1 else 2

-- The two distinct windows detect reversal errors: 1+4*2=9, but 4*1+2=6.
example : loop 4 1 bases (descending digits 2) 5 2 - (5 : ZMod 17) = 9 := by decide
example : loop 4 1 bases digits 5 2 - (5 : ZMod 17) = 6 := by decide
example : loop 4 1 bases (descending digits 2) 5 2 - (5 : ZMod 17) =
    ∑ j ∈ Finset.range 1, (∑ i ∈ Finset.range 2, 4^i * digits i j) • bases j := by
  simpa only [one_nsmul] using loop_correct 4 1 2 (by decide) bases digits (5 : ZMod 17)

-- The seed is suitable for setup and every actual addition, not just the final answer.
private theorem accepted : GroupAccepts 4 1 2 bases (descending digits 2) (5 : ZMod 17) := by
  apply groupAccepts_of_not_mem 4 1 2 (by decide) bases (descending digits 2) 5
  · intro u v he
    simpa using he
  · decide

private theorem radix_injective : Function.Injective (fun u : ZMod 17 => 4 • u) := by
  apply prime_radix_injective 4 1 (by decide) (by decide)
  · rw [Nat.card_eq_fintype_card]
    change Nat.Prime 17
    decide
  · rw [Nat.card_eq_fintype_card]
    change (4 : ℤ)*1+4-1 < 17
    decide

example : ∀ i, i ≤ 2 → loop 4 1 bases (descending digits 2) 5 i ≠ 0 :=
  loop_ne_zero 4 1 2 bases (descending digits 2) 5 accepted radix_injective

example : ∀ k, k ≤ 2 → 2^k • loop 4 1 bases (descending digits 2) 5 1 ≠ 0 := by
  intro k hk
  exact doubling_ready 2 1 2 bases (descending digits 2) 5 accepted radix_injective (by decide) hk

-- Exact cardinalities are kernel checked; overlapping exclusions make the bound conservative.
example : (loopBadSeeds 4 1 2 bases (descending digits 2)).card = 4 := by decide
example : (allBadSeeds 4 1 2 bases (descending digits 2)).card = 9 := by decide
example : failureBudget 4 1 2 = 10 := by decide

-- The normalized probability statement is instantiated on the same example.
example : (PMF.uniformOfFintype (ZMod 17)).toOuterMeasure
    {u | ¬ GroupAccepts 4 1 2 bases (descending digits 2) u} ≤ (10 : ℝ≥0∞)/17 := by
  have h := uniform_group_failure_bound_prime 4 1 2 (by decide) (by decide)
    bases (descending digits 2)
    (by rw [Nat.card_eq_fintype_card]; change Nat.Prime 17; decide)
    (by rw [Nat.card_eq_fintype_card]; change (4 : ℤ)*1+4-1 < 17; decide)
  simpa [failureBudget] using h

-- The same numerical parameters work for all bases and all fixed digit choices.
example (P : ℕ → ZMod 17) (s : ℕ → ℕ → ℕ) :
    ∃ u : ZMod 17, GroupAccepts 4 1 2 P s u := by
  apply exists_groupAccepts_prime 4 1 2 (by decide) (by decide) P s
  · rw [Nat.card_eq_fintype_card]
    change Nat.Prime 17
    decide
  · rw [Nat.card_eq_fintype_card]
    change (4 : ℤ)*1+4-1 < 17
    decide
  · change 10 < 17
    decide

-- A coefficient divisible by the group order need not exclude only one seed.
example : minusCoeff 4 2 0 = 5 := by decide
example : (Finset.univ.filter (fun u : ZMod 5 => minusCoeff 4 2 0 • u = 0)).card = 5 := by
  decide

-- Zero windows and empty base sums are still mathematically correct.
example (u : ZMod 17) : loop 4 0 bases digits u 3 = 0 := by
  simp [loop, addRows]
example (u : ZMod 17) : loop 4 1 bases digits u 0 - u = 0 := by
  simp [loop]

end EfficientFFA.Tests.MSM

-- Audit every theorem added in this milestone.
#print axioms EfficientFFA.MSM.addRows_eq
#print axioms EfficientFFA.MSM.loop_invariant
#print axioms EfficientFFA.MSM.horner_eq_sum
#print axioms EfficientFFA.MSM.loop_correct
#print axioms EfficientFFA.MSM.row_invariant
#print axioms EfficientFFA.MSM.affine_eq_iff
#print axioms EfficientFFA.MSM.collision_iff
#print axioms EfficientFFA.MSM.collision_coeff_bounds
#print axioms EfficientFFA.MSM.zsmul_injective_of_prime_card
#print axioms EfficientFFA.MSM.scalar_fiber_card_le_one
#print axioms EfficientFFA.MSM.mem_collisionSeeds_iff
#print axioms EfficientFFA.MSM.collisionSeeds_card_le
#print axioms EfficientFFA.MSM.loopBadSeeds_card_le
#print axioms EfficientFFA.MSM.loopBadSeeds_card_le_prime
#print axioms EfficientFFA.MSM.allBadSeeds_card_le
#print axioms EfficientFFA.MSM.groupAccepts_of_not_mem
#print axioms EfficientFFA.MSM.uniform_badSeeds_bound
#print axioms EfficientFFA.MSM.uniform_group_failure_bound
#print axioms EfficientFFA.MSM.prime_parameter_maps
#print axioms EfficientFFA.MSM.prime_radix_injective
#print axioms EfficientFFA.MSM.uniform_group_failure_bound_prime
#print axioms EfficientFFA.MSM.exists_groupAccepts_prime
#print axioms EfficientFFA.MSM.addRows_ne_zero
#print axioms EfficientFFA.MSM.loop_ne_zero
#print axioms EfficientFFA.MSM.row_ready
#print axioms EfficientFFA.MSM.doubling_ready
#print axioms EfficientFFA.EllipticCurve.Curve.msm_row_witnesses
#print axioms EfficientFFA.EllipticCurve.Curve.msm_double_witnesses
