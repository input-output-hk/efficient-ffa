import EfficientFFA.MSM.Collisions

open scoped ENNReal

namespace EfficientFFA.MSM
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Setup and loop exclusions for the same sampled seed. -/
def allBadSeeds (b l n : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) : Finset G :=
  badSeeds (fun j : Fin l => bases j.val) (b-1) ∪ loopBadSeeds b l n bases windows

/-- The total group-level failure budget. -/
def failureBudget (b l n : ℕ) : ℕ := 1 + l*(b+1) + 2*n*l

theorem allBadSeeds_card_le (b l n : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ)
    (hs : Function.Injective (fun u : G => (b-1) • u))
    (hinj : ∀ j, j < l →
      Function.Injective (fun u : G => plusCoeff b l j • u) ∧
      Function.Injective (fun u : G => minusCoeff b l j • u)) :
    (allBadSeeds b l n bases windows).card ≤ failureBudget b l n := by
  have ht := badSeeds_card_le (fun j : Fin l => bases j.val) (b-1) hs
  have hl := loopBadSeeds_card_le b l n bases windows hinj
  have hu := Finset.card_union_le
    (badSeeds (fun j : Fin l => bases j.val) (b-1)) (loopBadSeeds b l n bases windows)
  have hwidth : b-1+2 = b+1 := by omega
  rw [hwidth] at ht
  dsimp [allBadSeeds, failureBudget]
  omega

/-- Group-level guard and table conditions. Coordinate witness composition is separate. -/
def GroupAccepts (b l n : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (u : G) : Prop :=
  l • u ≠ 0 ∧
  (∀ j, j < l → TableSafe (bases j) ((b-1) • u) (b-1)) ∧
  (∀ i, i < n → ∀ j, j < l → ¬ Collision b l bases windows u i j)

/-- Outside the counted set, all group-level checks hold simultaneously. -/
theorem groupAccepts_of_not_mem (b l n : ℕ) (hb : 1 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G)
    (hl : Function.Injective (fun u : G => l • u))
    (hu : u ∉ allBadSeeds b l n bases windows) : GroupAccepts b l n bases windows u := by
  have ht : u ∉ badSeeds (fun j : Fin l => bases j.val) (b-1) :=
    fun hm => hu (Finset.mem_union_left _ hm)
  obtain ⟨hzero, htable⟩ := setup_safe_of_not_mem
    (fun j : Fin l => bases j.val) (by omega) hl ht
  refine ⟨hzero, fun j hj => htable ⟨j, hj⟩, ?_⟩
  intro i hi j hj hc
  apply hu
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨j, Finset.mem_range.mpr hj,
    (mem_collisionSeeds_iff b l (by omega) bases windows u i j).mpr hc⟩

/-- A normalized uniform sampler; the event is the explicit finite exclusion set. -/
theorem uniform_badSeeds_bound (b l n : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ)
    (hs : Function.Injective (fun u : G => (b-1) • u))
    (hinj : ∀ j, j < l →
      Function.Injective (fun u : G => plusCoeff b l j • u) ∧
      Function.Injective (fun u : G => minusCoeff b l j • u)) :
    (PMF.uniformOfFintype G).toOuterMeasure (allBadSeeds b l n bases windows : Set G) ≤
      (failureBudget b l n : ℝ≥0∞) / (Fintype.card G : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  apply mul_le_mul_left
  exact_mod_cast allBadSeeds_card_le b l n hb bases windows hs hinj

/-- Failure of the group-level conditions is bounded under uniform sampling. -/
theorem uniform_group_failure_bound (b l n : ℕ) (hb : 1 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ)
    (hs : Function.Injective (fun u : G => (b-1) • u))
    (hl : Function.Injective (fun u : G => l • u))
    (hinj : ∀ j, j < l →
      Function.Injective (fun u : G => plusCoeff b l j • u) ∧
      Function.Injective (fun u : G => minusCoeff b l j • u)) :
    (PMF.uniformOfFintype G).toOuterMeasure {u | ¬ GroupAccepts b l n bases windows u} ≤
      (failureBudget b l n : ℝ≥0∞) / (Fintype.card G : ℝ≥0∞) := by
  apply le_trans (show (PMF.uniformOfFintype G).toOuterMeasure
    {u | ¬ GroupAccepts b l n bases windows u} ≤
    (PMF.uniformOfFintype G).toOuterMeasure (allBadSeeds b l n bases windows : Set G) from ?_)
    (uniform_badSeeds_bound b l n (by omega) bases windows hs hinj)
  apply (PMF.uniformOfFintype G).toOuterMeasure.mono
  intro u hu
  by_contra hnot
  exact hu (groupAccepts_of_not_mem b l n hb bases windows u hl hnot)

omit [DecidableEq G] in
/-- Prime-cardinality parameters discharge the seed and collision injectivity obligations. -/
theorem prime_parameter_maps (b l : ℕ) (hb : 1 < b) (hl : 0 < l)
    (hq : Nat.Prime (Nat.card G)) (hsize : (b : ℤ)*l+b-1 < (Nat.card G : ℤ)) :
    Function.Injective (fun u : G => (b-1) • u) ∧
    Function.Injective (fun u : G => l • u) ∧
    ∀ j, j < l →
      Function.Injective (fun u : G => plusCoeff b l j • u) ∧
      Function.Injective (fun u : G => minusCoeff b l j • u) := by
  have hb' : (1 : ℤ) < b := by omega
  have hl' : (0 : ℤ) < l := by omega
  have hbl : (b : ℤ) < (Nat.card G : ℤ) := by nlinarith
  have hsl : b-1 < Nat.card G := by omega
  have hll : l < Nat.card G := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · exact (hq.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) hsl)).nsmul_right_bijective.injective
  · exact (hq.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hl hll)).nsmul_right_bijective.injective
  · intro j hj
    have hc := collision_coeff_bounds b l j (by omega) hj
    exact ⟨zsmul_injective_of_prime_card hq hc.1.1 (lt_of_le_of_lt hc.1.2 hsize),
      zsmul_injective_of_prime_card hq hc.2.1 (lt_of_le_of_lt hc.2.2 hsize)⟩

omit [Fintype G] [DecidableEq G] in
/-- The same prime-group size condition also preserves nonidentity through doubling. -/
theorem prime_radix_injective (b l : ℕ) (hb : 1 < b) (hl : 0 < l)
    (hq : Nat.Prime (Nat.card G)) (hsize : (b : ℤ)*l+b-1 < (Nat.card G : ℤ)) :
    Function.Injective (fun u : G => b • u) := by
  have hb' : (1 : ℤ) < b := by omega
  have hl' : (0 : ℤ) < l := by omega
  have hsmall : b < Nat.card G := by nlinarith
  exact (hq.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) hsmall)).nsmul_right_bijective.injective

/-- Numerical prime-group version of the full group-level rejection bound. -/
theorem uniform_group_failure_bound_prime (b l n : ℕ) (hb : 1 < b) (hl : 0 < l)
    (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (hq : Nat.Prime (Nat.card G))
    (hsize : (b : ℤ)*l+b-1 < (Nat.card G : ℤ)) :
    (PMF.uniformOfFintype G).toOuterMeasure {u | ¬ GroupAccepts b l n bases windows u} ≤
      (failureBudget b l n : ℝ≥0∞) / (Fintype.card G : ℝ≥0∞) := by
  obtain ⟨hs, hlmap, hmaps⟩ := prime_parameter_maps (G := G) b l hb hl hq hsize
  exact uniform_group_failure_bound b l n hb bases windows hs hlmap hmaps

/-- If the total budget is smaller than the group, one seed satisfies all conditions. -/
theorem exists_groupAccepts_prime (b l n : ℕ) (hb : 1 < b) (hl : 0 < l)
    (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (hq : Nat.Prime (Nat.card G))
    (hsize : (b : ℤ)*l+b-1 < (Nat.card G : ℤ))
    (hbudget : failureBudget b l n < Fintype.card G) :
    ∃ u : G, GroupAccepts b l n bases windows u := by
  obtain ⟨hs, hlmap, hmaps⟩ := prime_parameter_maps (G := G) b l hb hl hq hsize
  have hbound := allBadSeeds_card_le b l n (by omega) bases windows hs hmaps
  have hex : ∃ u : G, u ∉ allBadSeeds b l n bases windows := by
    by_contra! h
    have hall : allBadSeeds b l n bases windows = Finset.univ := by
      ext u
      simp [h u]
    rw [hall, Finset.card_univ] at hbound
    omega
  obtain ⟨u, hu⟩ := hex
  exact ⟨u, groupAccepts_of_not_mem b l n hb bases windows u hlmap hu⟩

end EfficientFFA.MSM
