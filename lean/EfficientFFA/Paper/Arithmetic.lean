import EfficientFFA.Normalization

namespace EfficientFFA.Paper

/-- Residue encoding is injective whenever the whole radix interval fits in q. -/
theorem residue_injective {n : ℕ} {B q : ℤ} (hB : 0 < B)
    (hcap : B^n ≤ q) {x y : Limbs n} (hx : WellFormed B x) (hy : WellFormed B y)
    (he : eval B x ≡ eval B y [ZMOD q]) : x = y := by
  have bx := eval_bounds hB hx
  have by' := eval_bounds hB hy
  apply eval_injective hB hx hy
  have h := he
  rw [Int.ModEq, Int.emod_eq_of_lt bx.1 (lt_of_lt_of_le bx.2 hcap),
    Int.emod_eq_of_lt by'.1 (lt_of_lt_of_le by'.2 hcap)] at h
  exact h

/-- Exactly when the radix interval exceeds q, distinct bounded limbs encode
one residue. In particular equality B^n=q is the injective boundary. -/
theorem duplicate_residues_iff {n : ℕ} {B q : ℤ} (hB : 0 < B) (hq : 0 < q) :
    (∃ x y : Limbs n, WellFormed B x ∧ WellFormed B y ∧ x ≠ y ∧
      eval B x ≡ eval B y [ZMOD q]) ↔ q < B^n := by
  constructor
  · rintro ⟨x, y, hx, hy, hne, he⟩
    by_contra h
    exact hne (residue_injective hB (le_of_not_gt h) hx hy he)
  · intro h
    obtain ⟨x, hx, ex⟩ := exists_limbs hB n (le_refl (0 : ℤ)) (pow_pos hB n)
    obtain ⟨y, hy, ey⟩ := exists_limbs hB n (le_of_lt hq) h
    refine ⟨x, y, hx, hy, ?_, ?_⟩
    · intro e
      have := congrArg (eval B) e
      rw [ex, ey] at this
      omega
    · simp [Int.ModEq, ex, ey]

/-- A fixed normalization parameter set supports every smaller tracked interval.
Its quotient shifts and widths are not changed when the input bound shrinks. -/
theorem normalization_input_mono {n r : ℕ} (P : Normalization.Parameters n r)
    {L : ℤ} (hL : L ≤ P.limit) {x : Limbs n}
    (hx : LazyArithmetic.Bounded (fun _ => -L) (fun _ => L) x) : P.InputBounded x := by
  intro i
  have := hx i
  constructor <;> dsimp at * <;> omega

theorem normalization_exists_below_limit {n r : ℕ} (P : Normalization.Parameters n r)
    (hp : P.Valid) (hcap : P.q ≤ P.B^n) {L : ℤ} (hL : L ≤ P.limit)
    {x : Limbs n} (hx : LazyArithmetic.Bounded (fun _ => -L) (fun _ => L) x) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts x z u v ∧ eval P.B z = eval P.B x % P.q :=
  P.normalization_exists hp.positive hp.widths hcap (normalization_input_mono P hL hx)

/-- Starting in [lo,hi], k additions of well-formed radix-B limbs stay in
[lo, hi + k*(B-1)]. This specifies both the initial interval and the count. -/
theorem accumulated_additions {n k : ℕ} {B : ℤ} {lo hi x : Limbs n}
    (hx : LazyArithmetic.Bounded lo hi x) (ys : Fin k → Limbs n)
    (hy : ∀ j, WellFormed B (ys j)) :
    LazyArithmetic.Bounded lo (fun i => hi i + (k : ℤ)*(B-1))
      (fun i => x i + ∑ j, ys j i) := by
  intro i
  have h0 : 0 ≤ ∑ j, ys j i := Finset.sum_nonneg (fun j _ => (hy j i).1)
  have h1 : (∑ j, ys j i) ≤ (k : ℤ)*(B-1) := by
    calc
      _ ≤ ∑ _j : Fin k, (B-1) := Finset.sum_le_sum (fun j _ => by have := hy j i; omega)
      _ = _ := by simp; ring
  have := hx i
  constructor <;> dsimp <;> linarith

/-- The paper's L/B scaling rule is a sufficient uniform condition. It is not
necessary for an individual input (zero, for example, permits any multiplier). -/
theorem scale_within_limit {n : ℕ} {B L c : ℤ} {x : Limbs n}
    (hx : WellFormed B x) (hc : |c| * B ≤ L) :
    LazyArithmetic.Bounded (fun _ => -L) (fun _ => L) (fun i => c*x i) := by
  intro i
  have hi := hx i
  have hb : x i ≤ B := le_of_lt hi.2
  have hmul := mul_le_mul_of_nonneg_left hb (abs_nonneg c)
  have hab : |c*x i| ≤ L := by
    rw [abs_mul, abs_of_nonneg hi.1]
    exact hmul.trans hc
  exact abs_le.mp hab

/-- Replacing each reduced coefficient by q-1 gives a loose count bound.
The comparison is non-strict, including zero limbs and degenerate parameters. -/
theorem tight_single_le_loose {n : ℕ} {B q : ℤ} (hB : 0 < B) (hq : 0 < q)
    (c : Fin n → ℤ) :
    (B-1) * (∑ i, c i % q) ≤ (B-1) * ((n : ℤ)*(q-1)) := by
  apply mul_le_mul_of_nonneg_left _ (by omega)
  calc
    _ ≤ ∑ _i : Fin n, (q-1) := Finset.sum_le_sum (fun i _ => by
      have := Int.emod_lt_of_pos (c i) hq; omega)
    _ = _ := by simp; ring

theorem tight_double_le_loose {n : ℕ} {B q : ℤ} (hq : 0 < q)
    (c : Fin n → Fin n → ℤ) :
    (B-1)^2 * (∑ i, ∑ j, c i j % q) ≤ (B-1)^2 * ((n : ℤ)^2*(q-1)) := by
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (q-1) := Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => by have := Int.emod_lt_of_pos (c i j) hq; omega))
    _ = _ := by simp; ring

/-- Division form of the sufficient scaling threshold, for positive radix. -/
theorem scale_within_limit_of_div {n : ℕ} {B L c : ℤ} (hB : 0 < B)
    {x : Limbs n} (hx : WellFormed B x) (hc : |c| ≤ L / B) :
    LazyArithmetic.Bounded (fun _ => -L) (fun _ => L) (fun i => c*x i) :=
  scale_within_limit hx ((Int.le_ediv_iff_mul_le hB).mp hc)

/-- Concrete accumulation budget for a signed initial interval. -/
theorem accumulated_within_limit {n k : ℕ} {B L initial : ℤ} (hB : 0 < B)
    {x : Limbs n} (hx : LazyArithmetic.Bounded (fun _ => -initial) (fun _ => initial) x)
    (ys : Fin k → Limbs n) (hy : ∀ j, WellFormed B (ys j))
    (hcount : initial + (k : ℤ)*(B-1) ≤ L) :
    LazyArithmetic.Bounded (fun _ => -L) (fun _ => L)
      (fun i => x i + ∑ j, ys j i) := by
  have hsum := accumulated_additions hx ys hy
  have hk : 0 ≤ (k : ℤ)*(B-1) := mul_nonneg (Nat.cast_nonneg k) (by omega)
  intro i
  have := hsum i
  constructor <;> dsimp at * <;> omega

/-- A precise sufficient version of the paper's radix-headroom heuristic. -/
theorem limb_product_lt_native {B p x y : ℤ} (hB : 0 < B) (hp : B^2 < p)
    (hx : 0 ≤ x ∧ x < B) (hy : 0 ≤ y ∧ y < B) : x*y < p := by
  have h := mul_le_mul (le_of_lt hx.2) (le_of_lt hy.2) hy.1 (le_of_lt hB)
  nlinarith

/-- If q is at least sqrt(p) and B is below it, capacity forces at least two
limbs. This replaces the informal 'much smaller' prose by explicit inequalities. -/
theorem two_limbs_of_headroom {n : ℕ} {B p q : ℤ} (hB : 0 < B) (hq : 0 < q)
    (hp : B^2 < p) (hlarge : p ≤ q^2) (hcap : q ≤ B^n) : 2 ≤ n := by
  by_contra h
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · norm_num at hcap
    nlinarith
  · norm_num at hcap
    nlinarith

end EfficientFFA.Paper
