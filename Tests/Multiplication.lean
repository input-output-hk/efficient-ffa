import EfficientFFA

namespace EfficientFFA.Tests.Multiplication
open EfficientFFA.Multiplication

-- A composite foreign modulus, radix three, noncoprime auxiliary moduli,
-- and different auxiliary witness widths. All parameter hypotheses hold.
def P : Parameters 2 2 where
  B := 3
  q := 8
  p := 131
  M := ![2, 4]
  t := 3
  tm := ![4, 5]

theorem valid : P.Valid := by
  constructor <;> constructor <;> decide

private theorem wf (a b : ℤ) (ha : 0 ≤ a ∧ a < 3) (hb : 0 ≤ b ∧ b < 3) :
    WellFormed P.B ![a, b] := by
  intro i
  fin_cases i
  · exact ha
  · exact hb

-- A nonzero product: 7 * 5 = 3 modulo 8, with computed witnesses.
example : P.witnessU ![1, 2] ![2, 1] ![0, 1] = 3 ∧
    P.witnessV ![1, 2] ![2, 1] ![0, 1] = ![6, 6] := by decide

example : P.Accepts ![1, 2] ![2, 1] ![0, 1] 3 ![6, 6] := by
  constructor <;> decide

-- Maximal limbs, and the zero output, exercise the upper quotient bound.
example : P.Accepts ![2, 2] ![2, 2] ![0, 0] 5 ![10, 10] := by
  constructor <;> decide

-- Zero inputs may produce the noncanonical representative 8 of zero.
-- Its unshifted quotient is -1, and its shifted witness is zero.
example : mulResidual P.B P.q ![0, 0] ![0, 0] ![2, 2] / P.q = -1 ∧
    P.witnessU ![0, 0] ![0, 0] ![2, 2] = 0 := by decide

example : P.Accepts ![0, 0] ![0, 0] ![2, 2] 0 ![0, 0] := by
  constructor <;> decide

example : eval P.B (![2, 2] : Limbs 2) = 8 ∧
    eval P.B (![2, 2] : Limbs 2) ≠ (0 * 0) % P.q := by decide

-- Exercise the public equivalence and canonical-output theorem.
example : ∃ u v, P.Accepts ![1, 2] ![2, 1] ![0, 1] u v := by
  apply (P.accepts_iff_multiplication valid
    (wf 1 2 (by decide) (by decide))
    (wf 2 1 (by decide) (by decide))
    (wf 0 1 (by decide) (by decide))).mpr
  decide

example : eval P.B (![0, 1] : Limbs 2) =
    (eval P.B (![1, 2] : Limbs 2) * eval P.B (![2, 1] : Limbs 2)) % P.q := by
  apply P.canonical_output valid.positive valid.nowrap
    (wf 1 2 (by decide) (by decide))
    (wf 2 1 (by decide) (by decide))
    (wf 0 1 (by decide) (by decide))
    (u := 3) (v := ![6, 6])
  · constructor <;> decide
  · decide

-- Ceiling(-5/3) is -1, whereas floor(-5/3) is -2.
example : -((5 : ℤ) / 3) = -1 ∧ (-5 : ℤ) / 3 = -2 := by norm_num
example (k : ℤ) (hlo : -5 ≤ k * 3) (hhi : k * 3 ≤ 8) : -1 ≤ k ∧ k ≤ 2 := by
  simpa using quotient_interval (by norm_num : (0 : ℤ) < 3) hlo hhi

-- Upper quotient bounds use floor even when an auxiliary numerator is negative.
-- With a large auxiliary modulus, Cm can be negative: it is not a magnitude.
example : let S : Parameters 2 1 :=
    { B := 3, q := 8, p := 269, M := ![100], t := 3, tm := ![1] }
    S.Cm 0 = -60 ∧ S.lmax 0 = -1 ∧
      S.Accepts ![1, 2] ![2, 1] ![0, 1] 3 ![0] := by
  dsimp
  refine ⟨by decide, by decide, ?_⟩
  constructor <;> decide

-- Here the native modulus alone is insufficient, although the full parameter
-- set is valid. A false output 10 for 0 * 0 passes the native check with u=10.
def Q : Parameters 2 1 where
  B := 4
  q := 13
  p := 127
  M := ![2]
  t := 4
  tm := ![5]

theorem q_valid : Q.Valid := by
  constructor <;> constructor <;> decide

example : (0 ≤ (10 : ℤ) ∧ 10 < Q.Umax) ∧
    Q.nativeResidual ![0, 0] ![0, 0] ![2, 2] 10 ≡ 0 [ZMOD Q.p] := by decide

example : ¬ ∃ u v, Q.Accepts ![0, 0] ![0, 0] ![2, 2] u v := by
  intro hacc
  have hm := (Q.accepts_iff_multiplication q_valid
    (x := ![0, 0]) (y := ![0, 0]) (z := ![2, 2])
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide)).mp hacc
  norm_num [eval, Q, Fin.sum_univ_two, Int.ModEq] at hm

-- Weakening the strict auxiliary endpoint would allow a nonzero multiple of p.
example : (127 : ℤ) ≡ 0 [ZMOD 127] ∧ (127 : ℤ) ≤ 127 ∧ (127 : ℤ) ≠ 0 := by
  norm_num [Int.ModEq]

end EfficientFFA.Tests.Multiplication

#print axioms EfficientFFA.Multiplication.weighted_sum_bounds
#print axioms EfficientFFA.Multiplication.weighted_product_bounds
#print axioms EfficientFFA.Multiplication.quotient_interval
#print axioms EfficientFFA.Multiplication.Parameters.residual_bounds
#print axioms EfficientFFA.Multiplication.Parameters.auxCore_bounds
#print axioms EfficientFFA.Multiplication.Parameters.nativeResidual_bounds
#print axioms EfficientFFA.Multiplication.Parameters.auxResidual_bounds
#print axioms EfficientFFA.Multiplication.Parameters.auxCore_congr
#print axioms EfficientFFA.Multiplication.Parameters.multiplication_sound
#print axioms EfficientFFA.Multiplication.Parameters.canonical_witnesses_accept
#print axioms EfficientFFA.Multiplication.Parameters.multiplication_complete
#print axioms EfficientFFA.Multiplication.Parameters.accepts_iff_multiplication
#print axioms EfficientFFA.Multiplication.Parameters.canonical_output
