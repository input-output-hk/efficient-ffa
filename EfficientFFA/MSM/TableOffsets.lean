import EfficientFFA.MSM.Tables

namespace EfficientFFA.MSM
variable {G : Type*} [AddCommGroup G]

theorem entry_eq_iff (base offset target : G) (i : ℕ) :
    entry base offset i = target ↔ offset = i • base - target := by
  constructor
  · intro h
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm offset target).trans (sub_eq_iff_eq_add.mp h).symm
  · intro h
    rw [h]
    dsimp [entry]
    abel

/-- For a nonempty sequence of additions, these are exactly the forbidden offsets.
Repetitions caused by torsion are deduplicated by the finite set. -/
def badOffsets [DecidableEq G] (base : G) (steps : ℕ) : Finset G :=
  (Finset.range (steps+1)).image (fun i => i • base) ∪ {-base}

variable [DecidableEq G]

theorem table_safe_iff_avoids (base offset : G) {steps : ℕ} (hs : 0 < steps) :
    TableSafe base offset steps ↔ offset ∉ badOffsets base steps := by
  constructor
  · intro hsafe hmem
    simp only [badOffsets, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton] at hmem
    rcases hmem with ⟨i, hi, he⟩ | he
    · apply hsafe.1 i (by omega)
      simp only [entry, ← he, sub_self]
    · apply (hsafe.2 0 hs).1
      simp [entry, he]
  · intro havoid
    have hmul : ∀ i, i ≤ steps → offset ≠ i • base := by
      intro i hi he
      apply havoid
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), he.symm⟩
    have hneg : offset ≠ -base := by
      intro he
      exact havoid (Finset.mem_union_right _ (Finset.mem_singleton.mpr he))
    constructor
    · intro i hi he
      exact hmul i hi ((entry_eq_iff base offset 0 i).mp he |>.trans (sub_zero _))
    · intro i hi
      constructor
      · intro he
        have hh := (entry_eq_iff base offset base i).mp he
        cases i with
        | zero => exact hneg (by simpa using hh)
        | succ i =>
          apply hmul i (by omega)
          simpa only [succ_nsmul, add_sub_cancel_right] using hh
      · intro he
        apply hmul (i+1) (by omega)
        simpa only [sub_neg_eq_add, succ_nsmul] using (entry_eq_iff base offset (-base) i).mp he

/-- At most steps+2 offsets are excluded, without a group-order assumption. -/
theorem badOffsets_card_le (base : G) (steps : ℕ) :
    (badOffsets base steps).card ≤ steps+2 := by
  have hu := Finset.card_union_le
    ((Finset.range (steps+1)).image (fun i => i • base)) {-base}
  have hi := Finset.card_image_le (s := Finset.range (steps+1)) (f := fun i => i • base)
  simp only [Finset.card_range, Finset.card_singleton] at hu hi
  dsimp [badOffsets]
  omega

end EfficientFFA.MSM

namespace EfficientFFA.EllipticCurve.Curve
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K) [DecidableEq C.Point]

/-- A finite offset avoids the explicitly enumerated bad set exactly when the
paper-style table equations have witnesses, under the initial guard. -/
theorem offset_table_iff_avoids {base V : Coordinates K} {steps : ℕ}
    (hbase : C.OnCurve base) (hV : C.OnCurve V) (hguard : base.x ≠ V.x) (hs : 0 < steps) :
    (∃ table : ℕ → Coordinates K, table 0 = opposite V ∧ MSM.TableChecks base table steps) ↔
      C.point V hV ∉ MSM.badOffsets (C.point base hbase) steps :=
  (C.offset_table_witnesses_iff hbase hV hguard).trans
    (MSM.table_safe_iff_avoids _ _ hs)

end EfficientFFA.EllipticCurve.Curve
