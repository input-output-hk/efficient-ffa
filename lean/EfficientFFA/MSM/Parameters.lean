import EfficientFFA.MSM.TableOffsets

namespace EfficientFFA.MSM
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Unsuitable random seeds for table construction or the initial accumulator.
The shared table offset is steps • U; each row has steps+1 entries. -/
def badSeeds {l : ℕ} (bases : Fin l → G) (steps : ℕ) : Finset G :=
  {0} ∪ Finset.univ.biUnion (fun j =>
    Finset.univ.filter (fun u => steps • u ∈ badOffsets (bases j) steps))

/-- Injectivity transports the excluded-offset bound back to random seeds. -/
theorem row_badSeeds_card_le (base : G) (steps : ℕ)
    (hinj : Function.Injective (fun u : G => steps • u)) :
    (Finset.univ.filter (fun u : G => steps • u ∈ badOffsets base steps)).card ≤
      steps + 2 := by
  apply le_trans (Finset.card_le_card_of_injOn (fun u : G => steps • u) ?_ ?_)
    (badOffsets_card_le base steps)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u _ v _ huv
    exact hinj huv

/-- One initial-accumulator exclusion and at most steps+2 exclusions per row. -/
theorem badSeeds_card_le {l : ℕ} (bases : Fin l → G) (steps : ℕ)
    (hinj : Function.Injective (fun u : G => steps • u)) :
    (badSeeds bases steps).card ≤ 1 + l * (steps + 2) := by
  have hrows : (Finset.univ.biUnion (fun j : Fin l =>
      Finset.univ.filter (fun u : G => steps • u ∈ badOffsets (bases j) steps))).card ≤
      l * (steps + 2) := by
    apply le_trans Finset.card_biUnion_le
    calc
      _ ≤ ∑ _j : Fin l, (steps + 2) :=
        Finset.sum_le_sum (fun j _ => row_badSeeds_card_le (bases j) steps hinj)
      _ = _ := by simp
  have hu := Finset.card_union_le ({0} : Finset G)
    (Finset.univ.biUnion (fun j =>
      Finset.univ.filter (fun u : G => steps • u ∈ badOffsets (bases j) steps)))
  simpa only [badSeeds, Finset.card_singleton] using le_trans hu (Nat.add_le_add_left hrows 1)

/-- Avoidance gives the actual setup properties, with no added table checks. -/
theorem setup_safe_of_not_mem {l steps : ℕ} (bases : Fin l → G) {u : G}
    (hs : 0 < steps) (hl : Function.Injective (fun u : G => l • u))
    (hu : u ∉ badSeeds bases steps) :
    l • u ≠ 0 ∧ ∀ j, TableSafe (bases j) (steps • u) steps := by
  have hu0 : u ≠ 0 := by
    intro he
    exact hu (by simp [badSeeds, he])
  constructor
  · intro he
    exact hu0 (hl (by simpa using he))
  · intro j
    apply (table_safe_iff_avoids _ _ hs).mpr
    intro hm
    apply hu
    simp only [badSeeds, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact Or.inr ⟨j, hm⟩

/-- Concrete cardinality and coprimality conditions guarantee an admissible seed.
For a window width w, use steps=2^w-1, giving the bound 1+l*(2^w+1). -/
theorem exists_safe_setup {l steps : ℕ} (bases : Fin l → G)
    (hs : 0 < steps) (hsteps : (Nat.card G).Coprime steps)
    (hl : (Nat.card G).Coprime l)
    (hsize : 1 + l * (steps + 2) < Fintype.card G) :
    ∃ u : G, l • u ≠ 0 ∧ ∀ j, TableSafe (bases j) (steps • u) steps := by
  have hb := badSeeds_card_le bases steps hsteps.nsmul_right_bijective.injective
  have hex : ∃ u : G, u ∉ badSeeds bases steps := by
    by_contra! h
    have hall : badSeeds bases steps = Finset.univ := by
      ext u
      simp [h u]
    rw [hall, Finset.card_univ] at hb
    omega
  obtain ⟨u, hu⟩ := hex
  exact ⟨u, setup_safe_of_not_mem bases hs hl.nsmul_right_bijective.injective hu⟩

/-- In a prime-cardinality group, positive scalars below the cardinality suffice. -/
theorem exists_safe_setup_prime {l steps : ℕ} (bases : Fin l → G)
    (hq : Nat.Prime (Nat.card G)) (hs : 0 < steps) (hl : 0 < l)
    (hsize : 1 + l * (steps + 2) < Fintype.card G) :
    ∃ u : G, l • u ≠ 0 ∧ ∀ j, TableSafe (bases j) (steps • u) steps := by
  have hsmallS : steps < Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    nlinarith
  have hsmallL : l < Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    nlinarith
  apply exists_safe_setup bases hs _ _ hsize
  · exact hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hs hsmallS)
  · exact hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hl hsmallL)

end EfficientFFA.MSM

namespace EfficientFFA.EllipticCurve.Curve
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)
variable [Fintype C.Point] [DecidableEq C.Point]

/-- Parameter selection yields actual affine table witnesses for every base.
Neither per-step guards nor the initial x-guard are extra hypotheses here. -/
theorem tables_exist_of_parameters {l steps : ℕ}
    (bases : Fin l → Coordinates K) (hbases : ∀ j, C.OnCurve (bases j))
    (hs : 0 < steps) (hsteps : (Nat.card C.Point).Coprime steps)
    (hl : (Nat.card C.Point).Coprime l)
    (hsize : 1 + l * (steps + 2) < Fintype.card C.Point) :
    ∃ u : C.Point, l • u ≠ 0 ∧ ∀ j,
      ∃ table : ℕ → Coordinates K,
        table 0 = C.coordinates (-(steps • u)) ∧
        (table 0).x ≠ (bases j).x ∧ MSM.TableChecks (bases j) table steps := by
  obtain ⟨u, hu, hsafe⟩ := MSM.exists_safe_setup
    (fun j => C.point (bases j) (hbases j)) hs hsteps hl hsize
  refine ⟨u, hu, fun j => ?_⟩
  have hstart : -(steps • u) ≠ 0 := by
    simpa only [MSM.entry, zero_nsmul, zero_sub] using (hsafe j).1 0 (by omega)
  obtain ⟨table, ht, hc⟩ := C.table_complete (hbases j) (C.coordinates_on_curve hstart)
    (C.point_coordinates hstart) (hsafe j)
  refine ⟨table, ht, ?_, hc⟩
  rw [ht]
  intro hx
  have he := (C.same_x_iff (C.coordinates_on_curve hstart) (hbases j)).mp hx
  rw [C.point_coordinates hstart] at he
  have hne := (hsafe j).2 0 hs
  simp only [MSM.entry, zero_nsmul, zero_sub] at hne
  exact he.elim hne.1 hne.2

end EfficientFFA.EllipticCurve.Curve
