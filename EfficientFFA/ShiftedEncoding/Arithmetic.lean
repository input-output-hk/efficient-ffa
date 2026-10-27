import EfficientFFA.ShiftedEncoding.Representation
import EfficientFFA.Normalization

namespace EfficientFFA.ShiftedEncoding
variable {n : ℕ}

/-- Add an integer correction to the least significant limb. -/
def bump (c : ℤ) (x : Limbs (n+1)) : Limbs (n+1) :=
  Fin.cons (x 0 + c) (fun i => x i.succ)

def add (x y : Limbs (n+1)) : Limbs (n+1) := bump 1 (fun i => x i + y i)
def sub (x y : Limbs (n+1)) : Limbs (n+1) := bump (-1) (fun i => x i - y i)
def neg (x : Limbs (n+1)) : Limbs (n+1) := bump (-2) (fun i => -x i)
def scale (c : ℤ) (x : Limbs (n+1)) : Limbs (n+1) := bump (c-1) (fun i => c*x i)

theorem eval_bump (B c : ℤ) (x : Limbs (n+1)) : eval B (bump c x) = eval B x + c := by
  rw [eval_head_tail, eval_head_tail B x]
  simp only [bump, Fin.cons_zero, Fin.cons_succ]
  ring

theorem value_add (B : ℤ) (x y : Limbs (n+1)) :
    value B (add x y) = value B x + value B y := by
  simp [value, add, eval_bump, eval_add]
  ring

theorem value_sub (B : ℤ) (x y : Limbs (n+1)) :
    value B (sub x y) = value B x - value B y := by
  simp only [value, sub, eval_bump, eval_sub]
  ring

theorem value_neg (B : ℤ) (x : Limbs (n+1)) : value B (neg x) = -value B x := by
  simp only [value, neg, eval_bump, LazyArithmetic.eval_neg]
  ring

/-- Addition of a plain integer constant needs only a low-limb correction. -/
theorem value_add_constant (B c : ℤ) (x : Limbs (n+1)) :
    value B (bump c x) = value B x + c := by
  simp only [value, eval_bump]
  ring

theorem value_scale (B c : ℤ) (x : Limbs (n+1)) :
    value B (scale c x) = c * value B x := by
  simp only [value, scale, eval_bump, eval_scale]
  ring

theorem bounded_bump (c : ℤ) {lo hi x : Limbs (n+1)}
    (hx : LazyArithmetic.Bounded lo hi x) :
    LazyArithmetic.Bounded (bump c lo) (bump c hi) (bump c x) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := hx 0
    simp only [bump, Fin.cons_zero]
    constructor <;> omega
  · exact hx _

theorem bounded_add {lo hi lo' hi' x y : Limbs (n+1)}
    (hx : LazyArithmetic.Bounded lo hi x) (hy : LazyArithmetic.Bounded lo' hi' y) :
    LazyArithmetic.Bounded (add lo lo') (add hi hi') (add x y) :=
  bounded_bump 1 (LazyArithmetic.bounded_add hx hy)

theorem bounded_sub {lo hi lo' hi' x y : Limbs (n+1)}
    (hx : LazyArithmetic.Bounded lo hi x) (hy : LazyArithmetic.Bounded lo' hi' y) :
    LazyArithmetic.Bounded (sub lo hi') (sub hi lo') (sub x y) :=
  bounded_bump (-1) (LazyArithmetic.bounded_sub hx hy)

theorem bounded_neg {lo hi x : Limbs (n+1)} (hx : LazyArithmetic.Bounded lo hi x) :
    LazyArithmetic.Bounded (neg hi) (neg lo) (neg x) :=
  bounded_bump (-2) (LazyArithmetic.bounded_neg hx)

theorem bounded_scale (c : ℤ) {lo hi x : Limbs (n+1)}
    (hx : LazyArithmetic.Bounded lo hi x) :
    LazyArithmetic.Bounded
      (bump (c-1) (fun i => if 0 ≤ c then c*lo i else c*hi i))
      (bump (c-1) (fun i => if 0 ≤ c then c*hi i else c*lo i)) (scale c x) :=
  bounded_bump (c-1) (LazyArithmetic.bounded_scale c hx)

theorem represents_bump {p c : ℤ} {sx sz x : Limbs (n+1)}
    (hx : LazyArithmetic.Represents p sx x)
    (hz : ∀ i, sz i ≡ bump c sx i [ZMOD p]) :
    LazyArithmetic.Represents p sz (bump c x) := by
  intro i
  apply (hz i).trans
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (hx 0).add (Int.ModEq.refl c)
  · exact hx _

theorem represents_add {p : ℤ} {sx sy sz x y : Limbs (n+1)}
    (hx : LazyArithmetic.Represents p sx x) (hy : LazyArithmetic.Represents p sy y)
    (hz : ∀ i, sz i ≡ add sx sy i [ZMOD p]) :
    LazyArithmetic.Represents p sz (add x y) :=
  represents_bump (LazyArithmetic.represents_add hx hy (fun _ => Int.ModEq.refl _)) hz

theorem represents_sub {p : ℤ} {sx sy sz x y : Limbs (n+1)}
    (hx : LazyArithmetic.Represents p sx x) (hy : LazyArithmetic.Represents p sy y)
    (hz : ∀ i, sz i ≡ sub sx sy i [ZMOD p]) :
    LazyArithmetic.Represents p sz (sub x y) :=
  represents_bump (LazyArithmetic.represents_sub hx hy (fun _ => Int.ModEq.refl _)) hz

theorem represents_neg {p : ℤ} {sx sz x : Limbs (n+1)}
    (hx : LazyArithmetic.Represents p sx x)
    (hz : ∀ i, sz i ≡ neg sx i [ZMOD p]) :
    LazyArithmetic.Represents p sz (neg x) :=
  represents_bump (LazyArithmetic.represents_neg hx (fun _ => Int.ModEq.refl _)) hz

theorem represents_scale {p : ℤ} {sx sz x : Limbs (n+1)} (c : ℤ)
    (hx : LazyArithmetic.Represents p sx x)
    (hz : ∀ i, sz i ≡ scale c sx i [ZMOD p]) :
    LazyArithmetic.Represents p sz (scale c x) :=
  represents_bump (LazyArithmetic.represents_scale c hx (fun _ => Int.ModEq.refl _)) hz

/-- The +1 offsets cancel, so normalization needs no altered constraints. -/
theorem value_congr_iff {k : ℕ} (B q : ℤ) (x z : Limbs k) :
    value B x ≡ value B z [ZMOD q] ↔ eval B x ≡ eval B z [ZMOD q] := by
  simp only [Int.modEq_iff_dvd, value, add_sub_add_left_eq_sub]

theorem normalization_iff {k r : ℕ} (P : Normalization.Parameters k r)
    (hP : P.Valid) {x z : Limbs k} (hx : P.InputBounded x) (hz : WellFormed P.B z) :
    (∃ u v, P.Accepts x z u v) ↔ value P.B x ≡ value P.B z [ZMOD P.q] :=
  (P.accepts_iff_normalization hP hx hz).trans (value_congr_iff P.B P.q x z).symm

/-- Stored native checks normalize the shifted interpretation as well. -/
theorem stored_normalization_sound {k r : ℕ} (P : Normalization.Parameters k r)
    (hP : P.Positive) (hnw : P.NoWrap) {stored x z : Limbs k} {u : ℤ} {v : Fin r → ℤ}
    (hs : LazyArithmetic.Represents P.p stored x) (hx : P.InputBounded x)
    (hz : WellFormed P.B z) (ha : P.Accepts stored z u v) :
    value P.B x ≡ value P.B z [ZMOD P.q] :=
  (value_congr_iff P.B P.q x z).mpr (P.stored_normalization_sound hP hnw hs hx hz ha)

/-- The selected shifted representative has integer value in [1,q], with q
representing zero. It is not a canonical residue in [0,q). -/
theorem stored_normalization_exists {k r : ℕ} (P : Normalization.Parameters k r)
    (hP : P.Positive) (hw : P.WidthBounds) (hcap : P.q ≤ P.B ^ k)
    {stored x : Limbs k} (hs : LazyArithmetic.Represents P.p stored x)
    (hx : P.InputBounded x) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts stored z u v ∧
      value P.B z = 1 + (value P.B x - 1) % P.q := by
  obtain ⟨z, u, v, hz, ha, he⟩ := P.stored_normalization_exists hP hw hcap hs hx
  refine ⟨z, u, v, hz, ha, ?_⟩
  simp only [value, he, add_sub_cancel_left]

end EfficientFFA.ShiftedEncoding
