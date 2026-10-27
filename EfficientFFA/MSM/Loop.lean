import EfficientFFA.MSM.Parameters

namespace EfficientFFA.MSM
variable {G : Type*} [AddCommGroup G]

/-- Sum of the first j unshifted table lookups in one window. -/
def rowSum (bases : ℕ → G) (digits : ℕ → ℕ) (j : ℕ) : G :=
  ∑ k ∈ Finset.range j, digits k • bases k

/-- The actual sequence of additions using offset table entries. -/
def addRows (bases : ℕ → G) (digits : ℕ → ℕ) (offset acc : G) : ℕ → G
  | 0 => acc
  | j+1 => addRows bases digits offset acc j + entry (bases j) offset (digits j)

theorem addRows_eq (bases : ℕ → G) (digits : ℕ → ℕ) (offset acc : G) (j : ℕ) :
    addRows bases digits offset acc j = acc + rowSum bases digits j - j • offset := by
  induction j with
  | zero => simp [addRows, rowSum]
  | succ j ih =>
    simp only [addRows, ih, rowSum, Finset.sum_range_succ, entry, succ_nsmul]
    abel

/-- Horner evaluation of windows in their processing order (most significant first). -/
def horner (b l : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) : ℕ → G
  | 0 => 0
  | i+1 => b • horner b l bases windows i + rowSum bases (windows i) l

/-- Offset MSM accumulator, before the final subtraction of l*U. -/
def loop (b l : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (u : G) : ℕ → G
  | 0 => l • u
  | i+1 => addRows bases (windows i) ((b-1) • u) (b • loop b l bases windows u i) l

/-- The shared offset is restored after each complete window. -/
theorem loop_invariant (b l : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G) (i : ℕ) :
    loop b l bases windows u i = horner b l bases windows i + l • u := by
  induction i with
  | zero => simp [loop, horner]
  | succ i ih =>
    rw [loop, addRows_eq, ih, horner, nsmul_add]
    have hmul : b * l = l * (b-1) + l := by
      have hsub : b-1+1 = b := Nat.sub_add_cancel hb
      nlinarith
    simp only [smul_smul, hmul, add_nsmul]
    abel

/-- Processing-order Horner evaluation as an explicit weighted sum. -/
theorem horner_eq_sum (b l : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (n : ℕ) :
    horner b l bases windows n =
      ∑ i ∈ Finset.range n, b^(n-1-i) • rowSum bases (windows i) l := by
  induction n with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner, ih, Finset.smul_sum, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hexp : n+1-1-i = (n-1-i)+1 := by omega
      rw [hexp, pow_succ, smul_smul, Nat.mul_comm]
    · simp

/-- Reverse little-endian windows before Horner evaluation. -/
def descending (windows : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → ℕ → ℕ :=
  fun i => windows (n-1-i)

/-- The final subtraction yields the intended little-endian scalar MSM. -/
theorem loop_correct (b l n : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G) :
    loop b l bases (descending windows n) u n - l • u =
      ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range n, b^i * windows i j) • bases j := by
  rw [loop_invariant b l hb, add_sub_cancel_right, horner_eq_sum]
  simp only [descending]
  rw [Finset.sum_range_reflect (fun i => b^i • rowSum bases (windows i) l) n]
  simp only [rowSum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.sum_smul).symm

/-- The unshifted component at row j of a window. -/
def rowValue (b l : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (i j : ℕ) : G :=
  b • horner b l bases windows i + rowSum bases (windows i) j

/-- The coefficient of U before row j; use integers to avoid truncated subtraction. -/
def offsetCoeff (b l j : ℕ) : ℤ := (b : ℤ)*l - ((b : ℤ)-1)*j

/-- The intermediate accumulator is affine in the sampled seed. -/
theorem row_invariant (b l : ℕ) (hb : 0 < b) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G) (i j : ℕ) :
    addRows bases (windows i) ((b-1) • u) (b • loop b l bases windows u i) j =
      rowValue b l bases windows i j + offsetCoeff b l j • u := by
  rw [addRows_eq, loop_invariant b l hb]
  have hbcast : ((b-1 : ℕ) : ℤ) = (b : ℤ)-1 := by omega
  simp only [rowValue, offsetCoeff]
  simp only [← Nat.cast_smul_eq_nsmul ℤ, hbcast]
  module

end EfficientFFA.MSM
