import EfficientFFA

namespace EfficientFFA.Tests.Parameters
open MSM

-- Positive prime-cardinality parameters make the setup existence theorem nonvacuous.
example (bases : Fin 2 → ZMod 17) :
    ∃ u : ZMod 17, 2 • u ≠ 0 ∧ ∀ j, TableSafe (bases j) (3 • u) 3 := by
  apply exists_safe_setup_prime bases
  · rw [Nat.card_eq_fintype_card]
    change Nat.Prime 17
    decide
  · decide
  · decide
  · change 1 + 2 * (3 + 2) < 17
    decide

-- Prime order is sufficient, not necessary: both scalar maps are invertible modulo 25.
example (bases : Fin 2 → ZMod 25) :
    ∃ u : ZMod 25, 2 • u ≠ 0 ∧ ∀ j, TableSafe (bases j) (3 • u) 3 := by
  apply exists_safe_setup bases (by decide)
  · rw [Nat.card_eq_fintype_card]
    change Nat.Coprime 25 3
    decide
  · rw [Nat.card_eq_fintype_card]
    change Nat.Coprime 25 2
    decide
  · change 1 + 2 * (3 + 2) < 25
    decide

-- If the offset scalar is not invertible, a larger group alone does not suffice.
-- Here every possible shared offset is 0 or 4, both excluded for base 4.
example : ¬ ∃ u : ZMod 8, TableSafe 4 (4 • u) 4 := by
  intro ⟨u, hu⟩
  have hbad : ∀ u : ZMod 8, 4 • u ∈ badOffsets (4 : ZMod 8) 4 := by decide
  exact (table_safe_iff_avoids 4 (4 • u) (by decide)).mp hu (hbad u)

-- A known rejected offset is excluded by the same finite set used in parameter selection.
example : (2 : ZMod 17) ∈ badOffsets (1 : ZMod 17) 3 := by decide

end EfficientFFA.Tests.Parameters

#print axioms EfficientFFA.MSM.row_badSeeds_card_le
#print axioms EfficientFFA.MSM.badSeeds_card_le
#print axioms EfficientFFA.MSM.setup_safe_of_not_mem
#print axioms EfficientFFA.MSM.exists_safe_setup
#print axioms EfficientFFA.MSM.exists_safe_setup_prime
#print axioms EfficientFFA.EllipticCurve.Curve.tables_exist_of_parameters
