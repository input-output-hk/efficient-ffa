import EfficientFFA.MSM.Loop

namespace EfficientFFA.MSM
variable {G : Type*} [AddCommGroup G]

def plusCoeff (b l j : ℕ) : ℤ := offsetCoeff b l j + ((b : ℤ)-1)
def minusCoeff (b l j : ℕ) : ℤ := offsetCoeff b l j - ((b : ℤ)-1)

/-- Either exceptional operand equality at an actual intermediate loop state. -/
def Collision (b l : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ)
    (u : G) (i j : ℕ) : Prop :=
  let acc := addRows bases (windows i) ((b-1) • u) (b • loop b l bases windows u i) j
  let aux := entry (bases j) ((b-1) • u) (windows i j)
  acc = aux ∨ acc = -aux

/-- Isolate the seed in an affine equality. -/
theorem affine_eq_iff (a d u : G) (c s : ℤ) :
    a + c • u = d - s • u ↔ (c+s) • u = d-a := by
  simp only [eq_sub_iff_add_eq, add_zsmul]
  constructor <;> intro h
  · calc
      c • u + s • u + a = a + c • u + s • u := by abel
      _ = d := h
  · calc
      a + c • u + s • u = c • u + s • u + a := by abel
      _ = d := h

/-- The two loop collision equations have seed coefficients independent of the digits. -/
theorem collision_iff (b l : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G) (i j : ℕ) :
    Collision b l bases windows u i j ↔
      plusCoeff b l j • u = (windows i j) • bases j - rowValue b l bases windows i j ∨
      minusCoeff b l j • u = -(windows i j • bases j) - rowValue b l bases windows i j := by
  unfold Collision
  rw [row_invariant b l hb]
  have hbcast : ((b-1 : ℕ) : ℤ) = (b : ℤ)-1 := by omega
  simp only [entry, ← Nat.cast_smul_eq_nsmul ℤ, hbcast]
  have hneg (d : G) : -(d - ((b : ℤ)-1) • u) = -d - (-((b : ℤ)-1)) • u := by
    simp only [neg_smul]
    abel
  rw [hneg, affine_eq_iff, affine_eq_iff]
  rfl

/-- Both coefficients are positive and bounded uniformly over the row index. -/
theorem collision_coeff_bounds (b l j : ℕ) (hb : 0 < b) (hj : j < l) :
    (0 < plusCoeff b l j ∧ plusCoeff b l j ≤ (b : ℤ)*l+b-1) ∧
    (0 < minusCoeff b l j ∧ minusCoeff b l j ≤ (b : ℤ)*l+b-1) := by
  have hb' : (1 : ℤ) ≤ b := by omega
  have hj' : (j : ℤ)+1 ≤ l := by omega
  have hprod := mul_le_mul_of_nonneg_left hj' (sub_nonneg.mpr hb')
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hprod0 := mul_nonneg (sub_nonneg.mpr hb') hj0
  dsimp [plusCoeff, minusCoeff, offsetCoeff]
  constructor <;> constructor <;> nlinarith

/-- A positive integer coefficient below prime group cardinality acts injectively. -/
theorem zsmul_injective_of_prime_card [Finite G] (hq : Nat.Prime (Nat.card G))
    {c : ℤ} (hc : 0 < c) (hsmall : c < (Nat.card G : ℤ)) :
    Function.Injective (fun u : G => c • u) := by
  have hnpos : 0 < c.toNat := by omega
  have hnlt : c.toNat < Nat.card G := by omega
  have hcop : (Nat.card G).Coprime c.toNat :=
    hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hnpos hnlt)
  have hinj : Function.Injective (fun u : G => c.toNat • u) :=
    hcop.nsmul_right_bijective.injective
  have hcast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg (by omega)
  simpa only [← Nat.cast_smul_eq_nsmul ℤ, hcast] using hinj

variable [Fintype G] [DecidableEq G]

/-- At most one seed solves an injective scalar equation. -/
theorem scalar_fiber_card_le_one (c : ℤ) (target : G)
    (hinj : Function.Injective (fun u : G => c • u)) :
    (Finset.univ.filter (fun u : G => c • u = target)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  exact hinj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)

/-- The union of the two scalar-equation fibers at one addition. -/
def collisionSeeds (b l : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ)
    (i j : ℕ) : Finset G :=
  Finset.univ.filter (fun u => plusCoeff b l j • u =
    windows i j • bases j - rowValue b l bases windows i j) ∪
  Finset.univ.filter (fun u => minusCoeff b l j • u =
    -(windows i j • bases j) - rowValue b l bases windows i j)

theorem mem_collisionSeeds_iff (b l : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G) (i j : ℕ) :
    u ∈ collisionSeeds b l bases windows i j ↔ Collision b l bases windows u i j := by
  simpa only [collisionSeeds, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    using (collision_iff b l hb bases windows u i j).symm

theorem collisionSeeds_card_le (b l : ℕ) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (i j : ℕ)
    (hplus : Function.Injective (fun u : G => plusCoeff b l j • u))
    (hminus : Function.Injective (fun u : G => minusCoeff b l j • u)) :
    (collisionSeeds b l bases windows i j).card ≤ 2 := by
  apply le_trans (Finset.card_union_le _ _)
  have hp := scalar_fiber_card_le_one (plusCoeff b l j)
    (windows i j • bases j - rowValue b l bases windows i j) hplus
  have hm := scalar_fiber_card_le_one (minusCoeff b l j)
    (-(windows i j • bases j) - rowValue b l bases windows i j) hminus
  omega

/-- All collisions over n windows and l additions per window. -/
def loopBadSeeds (b l n : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) : Finset G :=
  (Finset.range n).biUnion (fun i =>
    (Finset.range l).biUnion (fun j => collisionSeeds b l bases windows i j))

theorem loopBadSeeds_card_le (b l n : ℕ) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ)
    (hinj : ∀ j, j < l →
      Function.Injective (fun u : G => plusCoeff b l j • u) ∧
      Function.Injective (fun u : G => minusCoeff b l j • u)) :
    (loopBadSeeds b l n bases windows).card ≤ 2*n*l := by
  apply le_trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ _i ∈ Finset.range n, l*2 := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans Finset.card_biUnion_le
      calc
        _ ≤ ∑ _j ∈ Finset.range l, 2 := by
          apply Finset.sum_le_sum
          intro j hj
          exact collisionSeeds_card_le b l bases windows i j
            (hinj j (Finset.mem_range.mp hj)).1 (hinj j (Finset.mem_range.mp hj)).2
        _ = _ := by simp
    _ = _ := by simp; ring

/-- A direct numerical parameter rule discharges all collision-map obligations. -/
theorem loopBadSeeds_card_le_prime (b l n : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (hq : Nat.Prime (Nat.card G))
    (hsize : (b : ℤ)*l+b-1 < (Nat.card G : ℤ)) :
    (loopBadSeeds b l n bases windows).card ≤ 2*n*l := by
  apply loopBadSeeds_card_le
  intro j hj
  have hc := collision_coeff_bounds b l j hb hj
  exact ⟨zsmul_injective_of_prime_card hq hc.1.1 (lt_of_le_of_lt hc.1.2 hsize),
    zsmul_injective_of_prime_card hq hc.2.1 (lt_of_le_of_lt hc.2.2 hsize)⟩

end EfficientFFA.MSM
