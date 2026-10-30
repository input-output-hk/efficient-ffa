import EfficientFFA.Limbs

namespace EfficientFFA.LazyArithmetic
variable {n : ℕ}

/-- Inclusive bounds for the tracked integer value of each limb. -/
def Bounded (lo hi x : Limbs n) : Prop := ∀ i, lo i ≤ x i ∧ x i ≤ hi i

/-- Stored native residues represent tracked integers, which may be negative.
The stored values are not themselves interpreted as signed integer lifts. -/
def Represents (p : ℤ) (stored tracked : Limbs n) : Prop :=
  ∀ i, stored i ≡ tracked i [ZMOD p]

theorem bounded_add {lo hi lo' hi' x y : Limbs n}
    (hx : Bounded lo hi x) (hy : Bounded lo' hi' y) :
    Bounded (fun i => lo i + lo' i) (fun i => hi i + hi' i) (fun i => x i + y i) := by
  intro i
  have := hx i
  have := hy i
  constructor <;> dsimp <;> omega

theorem bounded_sub {lo hi lo' hi' x y : Limbs n}
    (hx : Bounded lo hi x) (hy : Bounded lo' hi' y) :
    Bounded (fun i => lo i - hi' i) (fun i => hi i - lo' i) (fun i => x i - y i) := by
  intro i
  have := hx i
  have := hy i
  constructor <;> dsimp <;> omega

theorem bounded_neg {lo hi x : Limbs n} (hx : Bounded lo hi x) :
    Bounded (fun i => -hi i) (fun i => -lo i) (fun i => -x i) := by
  intro i
  have := hx i
  constructor <;> dsimp <;> omega

theorem bounded_add_constant {lo hi x : Limbs n} (c : Limbs n)
    (hx : Bounded lo hi x) :
    Bounded (fun i => lo i + c i) (fun i => hi i + c i) (fun i => x i + c i) :=
  bounded_add hx (fun _ => ⟨le_rfl, le_rfl⟩)

theorem bounded_scale (c : ℤ) {lo hi x : Limbs n} (hx : Bounded lo hi x) :
    Bounded (fun i => if 0 ≤ c then c * lo i else c * hi i)
      (fun i => if 0 ≤ c then c * hi i else c * lo i) (fun i => c * x i) := by
  intro i
  have h := hx i
  split_ifs with hc
  · exact ⟨mul_le_mul_of_nonneg_left h.1 hc, mul_le_mul_of_nonneg_left h.2 hc⟩
  · have hc' : c ≤ 0 := by omega
    exact ⟨mul_le_mul_of_nonpos_left h.2 hc', mul_le_mul_of_nonpos_left h.1 hc'⟩

theorem represents_reduced (p : ℤ) (x : Limbs n) :
    Represents p (fun i => x i % p) x := by
  intro i
  simp [Int.ModEq]

theorem represents_add {p : ℤ} {sx sy sz x y : Limbs n}
    (hx : Represents p sx x) (hy : Represents p sy y)
    (hz : ∀ i, sz i ≡ sx i + sy i [ZMOD p]) :
    Represents p sz (fun i => x i + y i) :=
  fun i => (hz i).trans ((hx i).add (hy i))

theorem represents_sub {p : ℤ} {sx sy sz x y : Limbs n}
    (hx : Represents p sx x) (hy : Represents p sy y)
    (hz : ∀ i, sz i ≡ sx i - sy i [ZMOD p]) :
    Represents p sz (fun i => x i - y i) :=
  fun i => (hz i).trans ((hx i).sub (hy i))

theorem represents_neg {p : ℤ} {sx sz x : Limbs n}
    (hx : Represents p sx x) (hz : ∀ i, sz i ≡ -sx i [ZMOD p]) :
    Represents p sz (fun i => -x i) :=
  fun i => (hz i).trans (hx i).neg

theorem represents_add_constant {p : ℤ} {sx sz x : Limbs n} (c : Limbs n)
    (hx : Represents p sx x) (hz : ∀ i, sz i ≡ sx i + c i [ZMOD p]) :
    Represents p sz (fun i => x i + c i) :=
  fun i => (hz i).trans ((hx i).add (Int.ModEq.refl _))

theorem represents_scale {p : ℤ} {sx sz x : Limbs n} (c : ℤ)
    (hx : Represents p sx x) (hz : ∀ i, sz i ≡ c * sx i [ZMOD p]) :
    Represents p sz (fun i => c * x i) :=
  fun i => (hz i).trans ((Int.ModEq.refl c).mul (hx i))

theorem eval_neg (B : ℤ) (x : Limbs n) :
    eval B (fun i => -x i) = -eval B x := by
  simpa using eval_scale B (-1) x

/-- Short intervals give unique lifts; representation alone does not. -/
theorem lift_unique {p : ℤ} {lo hi x y stored : Limbs n}
    (hx : Bounded lo hi x) (hy : Bounded lo hi y)
    (hsx : Represents p stored x) (hsy : Represents p stored y)
    (hwidth : ∀ i, hi i - lo i < p) : x = y := by
  funext i
  have hm : x i - y i ≡ 0 [ZMOD p] := by
    simpa using ((hsx i).symm.trans (hsy i)).sub (Int.ModEq.refl (y i))
  have hxi := hx i
  have hyi := hy i
  have hw := hwidth i
  have hz := eq_zero_of_modEq_of_bounds hm (by omega) (by omega)
  omega

end EfficientFFA.LazyArithmetic
