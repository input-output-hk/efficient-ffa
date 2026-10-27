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

end EfficientFFA
