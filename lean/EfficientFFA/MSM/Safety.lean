import EfficientFFA.MSM.Rejection

namespace EfficientFFA.MSM
variable {G : Type*} [AddCommGroup G]

/-- No opposite-operand collision means the row additions remain nonidentity. -/
theorem addRows_ne_zero (bases : ℕ → G) (digits : ℕ → ℕ) (offset acc : G) (j : ℕ)
    (hacc : acc ≠ 0)
    (hsafe : ∀ k, k < j →
      addRows bases digits offset acc k ≠ -entry (bases k) offset (digits k)) :
    addRows bases digits offset acc j ≠ 0 := by
  cases j with
  | zero => exact hacc
  | succ j =>
    rw [addRows]
    exact fun he => hsafe j (by omega) (add_eq_zero_iff_eq_neg.mp he)

/-- Window-boundary accumulators remain finite when the radix map is injective. -/
theorem loop_ne_zero (b l n : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (u : G)
    (haccept : GroupAccepts b l n bases windows u)
    (hbmap : Function.Injective (fun u : G => b • u)) :
    ∀ i, i ≤ n → loop b l bases windows u i ≠ 0 := by
  intro i
  induction i with
  | zero => intro _; exact haccept.1
  | succ i ih =>
    intro hi
    rw [loop]
    apply addRows_ne_zero
    · intro he
      exact ih (by omega) (hbmap (by simpa using he))
    · intro j hj he
      exact haccept.2.2 i (by omega) j hj (Or.inr he)

/-- Actual operands satisfy the finite-input and distinct-x group preconditions.
The window range premise makes the auxiliary a lookup in the verified table. -/
theorem row_ready (b l n : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (u : G)
    (haccept : GroupAccepts b l n bases windows u)
    (hbmap : Function.Injective (fun u : G => b • u))
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < b)
    {i j : ℕ} (hi : i < n) (hj : j < l) :
    let acc := addRows bases (windows i) ((b-1) • u) (b • loop b l bases windows u i) j
    let aux := entry (bases j) ((b-1) • u) (windows i j)
    acc ≠ 0 ∧ aux ≠ 0 ∧ acc ≠ aux ∧ acc ≠ -aux := by
  dsimp
  have hcoll := haccept.2.2 i hi j hj
  refine ⟨?_, ?_, fun he => hcoll (Or.inl he), fun he => hcoll (Or.inr he)⟩
  · apply addRows_ne_zero
    · intro he
      exact loop_ne_zero b l n bases windows u haccept hbmap i (by omega)
        (hbmap (by simpa using he))
    · intro k hk he
      exact haccept.2.2 i hi k (by omega) (Or.inr he)
  · exact (haccept.2.1 j hj).1 (windows i j) (by have := hrange i hi j hj; omega)

/-- Every intermediate doubling is finite if the complete window multiplier is injective. -/
theorem doubling_ready (w l n : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (u : G)
    (haccept : GroupAccepts (2^w) l n bases windows u)
    (hbmap : Function.Injective (fun u : G => 2^w • u))
    {i k : ℕ} (hi : i ≤ n) (hk : k ≤ w) :
    2^k • loop (2^w) l bases windows u i ≠ 0 := by
  intro he
  have hpow : 2^w = 2^(w-k) * 2^k := by rw [← pow_add, Nat.sub_add_cancel hk]
  apply loop_ne_zero (2^w) l n bases windows u haccept hbmap i hi
  apply hbmap
  change 2^w • MSM.loop (2^w) l bases windows u i = 2^w • (0 : G)
  calc
    _ = (2^(w-k)*2^k) • MSM.loop (2^w) l bases windows u i :=
      congrArg (fun c : ℕ => c • MSM.loop (2^w) l bases windows u i) hpow
    _ = 0 := by rw [mul_smul, he, smul_zero]
    _ = _ := (smul_zero _).symm

end EfficientFFA.MSM

namespace EfficientFFA.EllipticCurve.Curve
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

/-- The group-level row conditions construct actual affine addition witnesses.
This is a local witness bridge; arbitrary supplied coordinate traces are separate. -/
theorem msm_row_witnesses (b l n : ℕ) (bases : ℕ → C.Point)
    (windows : ℕ → ℕ → ℕ) (u : C.Point)
    (haccept : MSM.GroupAccepts b l n bases windows u)
    (hbmap : Function.Injective (fun u : C.Point => b • u))
    (hrange : ∀ i, i < n → ∀ j, j < l → windows i j < b)
    {i j : ℕ} (hi : i < n) (hj : j < l) :
    let acc := MSM.addRows bases (windows i) ((b-1) • u)
      (b • MSM.loop b l bases windows u i) j
    let aux := MSM.entry (bases j) ((b-1) • u) (windows i j)
    (C.coordinates acc).x ≠ (C.coordinates aux).x ∧
    ∃ slope, AddChecks (C.coordinates acc) (C.coordinates aux) (C.coordinates (acc+aux)) slope := by
  let acc := MSM.addRows bases (windows i) ((b-1) • u) (b • MSM.loop b l bases windows u i) j
  let aux := MSM.entry (bases j) ((b-1) • u) (windows i j)
  change (C.coordinates acc).x ≠ (C.coordinates aux).x ∧
    ∃ slope, AddChecks (C.coordinates acc) (C.coordinates aux) (C.coordinates (acc+aux)) slope
  obtain ⟨ha, hb, heq, hneg⟩ := MSM.row_ready b l n bases windows u haccept hbmap hrange hi hj
  have hxa := C.coordinates_on_curve ha
  have hxb := C.coordinates_on_curve hb
  have hx : (C.coordinates acc).x ≠ (C.coordinates aux).x := by
    intro h
    have hh := (C.same_x_iff hxa hxb).mp h
    rw [C.point_coordinates ha, C.point_coordinates hb] at hh
    exact hh.elim heq hneg
  refine ⟨hx, ?_⟩
  obtain ⟨R, slope, hc, hR, hsum⟩ := C.addition_complete hxa hxb hx
  have hnonzero := fun h => hneg (add_eq_zero_iff_eq_neg.mp h)
  have hRcoords : R = C.coordinates (acc + aux) := by
    apply C.point_injective (hP := hR) (hQ := C.coordinates_on_curve hnonzero)
    simpa only [C.point_coordinates ha, C.point_coordinates hb,
      C.point_coordinates hnonzero] using hsum
  exact ⟨slope, by simpa only [hRcoords] using hc⟩

/-- Finite doubling states give the paper's tangent witnesses without an extra guard. -/
theorem msm_double_witnesses (w l n : ℕ) (bases : ℕ → C.Point)
    (windows : ℕ → ℕ → ℕ) (u : C.Point)
    (haccept : MSM.GroupAccepts (2^w) l n bases windows u)
    (hbmap : Function.Injective (fun u : C.Point => 2^w • u))
    {i k : ℕ} (hi : i < n) (hk : k < w) :
    ∃ slope, DoubleChecks C
      (C.coordinates (2^k • MSM.loop (2^w) l bases windows u i))
      (C.coordinates (2^(k+1) • MSM.loop (2^w) l bases windows u i)) slope := by
  have ha := MSM.doubling_ready w l n bases windows u haccept hbmap (Nat.le_of_lt hi) (Nat.le_of_lt hk)
  have hb := MSM.doubling_ready w l n bases windows u haccept hbmap (Nat.le_of_lt hi) (Nat.succ_le_of_lt hk)
  have hsum : 2^k • MSM.loop (2^w) l bases windows u i +
      2^k • MSM.loop (2^w) l bases windows u i =
      2^(k+1) • MSM.loop (2^w) l bases windows u i := by
    rw [pow_succ, mul_comm, mul_smul, two_smul]
  have hden : 2 * (C.coordinates (2^k • MSM.loop (2^w) l bases windows u i)).y ≠ 0 := by
    intro h
    have he := (C.double_eq_zero_iff (C.coordinates_on_curve ha)).mpr h
    rw [C.point_coordinates ha, hsum] at he
    exact hb he
  obtain ⟨R, slope, hc, hR, he⟩ := C.doubling_complete (C.coordinates_on_curve ha) hden
  have hRcoords : R = C.coordinates (2^(k+1) • MSM.loop (2^w) l bases windows u i) := by
    apply C.point_injective (hP := hR) (hQ := C.coordinates_on_curve hb)
    simpa only [C.point_coordinates ha, C.point_coordinates hb, hsum] using he
  exact ⟨slope, by simpa only [hRcoords] using hc⟩

end EfficientFFA.EllipticCurve.Curve
