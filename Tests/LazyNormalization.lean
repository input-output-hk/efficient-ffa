import EfficientFFA

namespace EfficientFFA.Tests.LazyNormalization
open LazyArithmetic

-- Negative constants reverse endpoint order.
example {lo hi x : Limbs 2} (hx : Bounded lo hi x) :
    Bounded (fun i => -2 * hi i) (fun i => -2 * lo i) (fun i => -2 * x i) := by
  simpa using bounded_scale (-2) hx

-- The same stored residue can have different tracked integer lifts.
example : Represents 13 (![12] : Limbs 1) ![-1] ∧
    Represents 13 (![12] : Limbs 1) ![12] := by dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]; decide
example : ¬ ((-1 : ℤ) ≡ 12 [ZMOD 8]) := by decide

example (x y : Limbs 1) (hx : Bounded ![-2] ![2] x) (hy : Bounded ![-2] ![2] y)
    (hsx : Represents 13 ![12] x) (hsy : Represents 13 ![12] y) : x = y := by
  exact lift_unique hx hy hsx hsy (by intro i; fin_cases i; decide)

-- A full normalization instance with signed limbs and noncoprime auxiliary moduli.
def P : Normalization.Parameters 2 2 where
  limit := 5
  B := 3
  q := 8
  p := 131
  M := ![2, 4]
  t := 3
  tm := ![4, 5]

theorem valid : P.Valid := by
  constructor <;> constructor <;> decide

-- -1 is stored as 130 modulo 131, then normalized to 7 modulo 8.
example : Represents P.p (![130, 0] : Limbs 2) ![-1, 0] := by dsimp [Represents]; decide
example : P.Accepts ![130, 0] ![1, 2] 3 ![6, 6] := by
  constructor <;> decide
example : P.witnessU ![-1, 0] ![1, 2] = 3 ∧
    P.witnessV ![-1, 0] ![1, 2] = ![6, 6] := by decide
example : eval P.B (![-1, 0] : Limbs 2) ≡ eval P.B (![1, 2] : Limbs 2) [ZMOD P.q] := by
  exact P.stored_normalization_sound valid.positive valid.nowrap
    (stored := ![130, 0]) (u := 3) (v := ![6, 6])
    (by dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]; decide) (by dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]; decide) (by dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]; decide) (by constructor <;> decide)

-- Exercise both endpoints of the signed input interval, and zero.
example : P.Accepts ![-5, -5] ![1, 1] 1 ![2, 2] := by constructor <;> decide
example : P.Accepts ![5, 5] ![1, 1] 6 ![12, 12] := by constructor <;> decide
example : P.Accepts ![0, 0] ![0, 0] 4 ![8, 8] := by constructor <;> decide

-- The public construction works for all bounded inputs, not just the examples.
example (x : Limbs 2) (hx : P.InputBounded x) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts x z u v ∧ eval P.B z = eval P.B x % P.q :=
  P.normalization_exists valid.positive valid.widths (by decide) hx

-- A native subtraction followed by the real normalization checks.
example : eval P.B (![0, 0] : Limbs 2) - eval P.B (![1, 0] : Limbs 2) ≡
    eval P.B (![1, 2] : Limbs 2) [ZMOD P.q] := by
  apply P.subtraction_normalization_sound valid.positive valid.nowrap
    (sx := ![0, 0]) (sy := ![1, 0]) (stored := ![130, 0]) (u := 3) (v := ![6, 6])
  · dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]
    decide
  · dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]
    decide
  · decide
  · dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]
    decide
  · dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]
    decide
  · constructor <;> decide

-- Wrong output zero is rejected regardless of the quotient witnesses.
example : ¬ ∃ u v, P.Accepts ![130, 0] ![0, 0] u v := by
  rintro ⟨u, v, ha⟩
  have hm := P.stored_normalization_sound valid.positive valid.nowrap
    (x := ![-1, 0]) (by dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]; decide) (by dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]; decide) (by dsimp [Represents, Normalization.Parameters.InputBounded, Bounded, WellFormed]; decide) ha
  norm_num [eval, P, Fin.sum_univ_two, Int.ModEq] at hm

-- Capacity matters: a single base-three limb cannot represent the residue seven.
example : ¬ ∃ z : Limbs 1, WellFormed 3 z ∧ eval 3 z = 7 := by
  rintro ⟨z, hz, he⟩
  have h := hz 0
  simp [eval] at he
  omega

-- Nonzero does not imply invertible over a composite modulus.
example : ¬ ((2 : ℤ) ≡ 0 [ZMOD 8]) ∧ ¬ ∃ b : ℤ, 2 * b ≡ 1 [ZMOD 8] := by
  constructor
  · decide
  · rw [Division.inverse_exists_iff_coprime, Int.isCoprime_iff_gcd_eq_one]
    decide

-- A nonunit also makes the naive division equation nonunique.
example : (2 : ℤ) * 1 ≡ 2 [ZMOD 8] ∧ (2 : ℤ) * 5 ≡ 2 [ZMOD 8] ∧
    ¬ ((1 : ℤ) ≡ 5 [ZMOD 8]) := by decide

example : ∃ inv : ℤ, (2 - 5) * inv ≡ 1 [ZMOD 7] := by
  apply (Division.prime_disequality_iff 7 (by decide) 2 5).mpr
  decide

end EfficientFFA.Tests.LazyNormalization

-- Trust audit for every new library theorem.
#print axioms EfficientFFA.LazyArithmetic.bounded_add
#print axioms EfficientFFA.LazyArithmetic.bounded_sub
#print axioms EfficientFFA.LazyArithmetic.bounded_neg
#print axioms EfficientFFA.LazyArithmetic.bounded_add_constant
#print axioms EfficientFFA.LazyArithmetic.bounded_scale
#print axioms EfficientFFA.LazyArithmetic.represents_reduced
#print axioms EfficientFFA.LazyArithmetic.represents_add
#print axioms EfficientFFA.LazyArithmetic.represents_sub
#print axioms EfficientFFA.LazyArithmetic.represents_neg
#print axioms EfficientFFA.LazyArithmetic.represents_add_constant
#print axioms EfficientFFA.LazyArithmetic.represents_scale
#print axioms EfficientFFA.LazyArithmetic.eval_neg
#print axioms EfficientFFA.LazyArithmetic.lift_unique
#print axioms EfficientFFA.exists_limbs
#print axioms EfficientFFA.exists_canonical_limbs
#print axioms EfficientFFA.Normalization.residual_mod
#print axioms EfficientFFA.Normalization.residual_dvd_iff
#print axioms EfficientFFA.Normalization.normalization_iff_quotient
#print axioms EfficientFFA.Normalization.weighted_linear_bounds
#print axioms EfficientFFA.Normalization.Parameters.residual_bounds
#print axioms EfficientFFA.Normalization.Parameters.auxCore_bounds
#print axioms EfficientFFA.Normalization.Parameters.nativeResidual_bounds
#print axioms EfficientFFA.Normalization.Parameters.auxResidual_bounds
#print axioms EfficientFFA.Normalization.Parameters.auxCore_congr
#print axioms EfficientFFA.Normalization.Parameters.normalization_sound
#print axioms EfficientFFA.Normalization.Parameters.canonical_witnesses_accept
#print axioms EfficientFFA.Normalization.Parameters.normalization_complete
#print axioms EfficientFFA.Normalization.Parameters.accepts_iff_normalization
#print axioms EfficientFFA.Normalization.Parameters.normalization_exists
#print axioms EfficientFFA.Normalization.Parameters.nativeResidual_congr
#print axioms EfficientFFA.Normalization.Parameters.auxResidual_congr
#print axioms EfficientFFA.Normalization.Parameters.accepts_of_rep
#print axioms EfficientFFA.Normalization.Parameters.stored_normalization_sound
#print axioms EfficientFFA.Normalization.Parameters.stored_normalization_exists
#print axioms EfficientFFA.Normalization.Parameters.subtraction_normalization_sound
#print axioms EfficientFFA.Division.inverse_exists_iff_coprime
#print axioms EfficientFFA.Division.division_iff
#print axioms EfficientFFA.Division.prime_inverse_iff
#print axioms EfficientFFA.Division.prime_disequality_iff
#print axioms EfficientFFA.Division.encoded_division_iff
#print axioms EfficientFFA.Division.encoded_inverse_iff
