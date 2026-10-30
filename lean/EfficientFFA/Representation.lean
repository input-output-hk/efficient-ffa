import EfficientFFA.Limbs

namespace EfficientFFA

/-- Every nonnegative integer below the radix capacity has bounded limbs.
This includes radix one and zero limbs, whose only represented value is zero. -/
theorem exists_limbs {B : ℤ} (hB : 0 < B) (n : ℕ) {a : ℤ}
    (ha : 0 ≤ a) (hcap : a < B ^ n) :
    ∃ z : Limbs n, WellFormed B z ∧ eval B z = a := by
  induction n generalizing a with
  | zero =>
    have ha0 : a = 0 := by
      norm_num at hcap
      omega
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · simp [eval, ha0]
  | succ n ih =>
    have hquot : a / B < B ^ n := by
      apply (Int.ediv_lt_iff_lt_mul hB).mpr
      simpa [pow_succ] using hcap
    obtain ⟨z, hz, he⟩ := ih (Int.ediv_nonneg ha (le_of_lt hB)) hquot
    refine ⟨Fin.cons (a % B) z, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨Int.emod_nonneg _ (ne_of_gt hB), Int.emod_lt_of_pos _ hB⟩
      · exact hz j
    · unfold eval
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_mul,
        Fin.val_succ, pow_succ]
      have ht : (∑ i : Fin n, B ^ i.val * B * z i) = B * eval B z := by
        simp only [eval, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [ht, he, mul_comm B]
      exact Int.emod_add_ediv_mul a B

/-- A canonical foreign residue is representable once q fits in the radix capacity. -/
theorem exists_canonical_limbs {B q : ℤ} (hB : 0 < B) (hq : 0 < q)
    (n : ℕ) (hcap : q ≤ B ^ n) (a : ℤ) :
    ∃ z : Limbs n, WellFormed B z ∧ eval B z = a % q :=
  exists_limbs hB n (Int.emod_nonneg _ (ne_of_gt hq))
    (lt_of_lt_of_le (Int.emod_lt_of_pos _ hq) hcap)

/-- Separate the least significant limb from the remaining radix expansion. -/
theorem eval_head_tail {n : ℕ} (B : ℤ) (x : Limbs (n+1)) :
    eval B x = x 0 + B * eval B (fun i => x i.succ) := by
  unfold eval
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A bounded radix expansion lies strictly below its capacity. -/
theorem eval_bounds {n : ℕ} {B : ℤ} (hB : 0 < B) {x : Limbs n}
    (hx : WellFormed B x) : 0 ≤ eval B x ∧ eval B x < B ^ n := by
  induction n with
  | zero => simp [eval]
  | succ n ih =>
    have ht := ih (x := fun i => x i.succ) (fun i => hx i.succ)
    have hh := hx 0
    rw [eval_head_tail, pow_succ]
    constructor <;> nlinarith

/-- Bounded radix expansions of the same integer have identical limbs. -/
theorem eval_injective {n : ℕ} {B : ℤ} (hB : 0 < B) {x y : Limbs n}
    (hx : WellFormed B x) (hy : WellFormed B y) (he : eval B x = eval B y) : x = y := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [eval_head_tail, eval_head_tail] at he
    have hh : x 0 = y 0 := by
      have hm := congrArg (fun a : ℤ => a % B) he
      simpa [Int.add_emod, Int.mul_emod,
        Int.emod_eq_of_lt (hx 0).1 (hx 0).2,
        Int.emod_eq_of_lt (hy 0).1 (hy 0).2] using hm
    have ht : eval B (fun i => x i.succ) = eval B (fun i => y i.succ) := by nlinarith
    have hi := ih (fun i => hx i.succ) (fun i => hy i.succ) ht
    funext i
    exact Fin.cases hh (fun j => congrFun hi j) i

end EfficientFFA
