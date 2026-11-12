import EfficientFFA.Native.Expression
import EfficientFFA.ShiftedEncoding.Representation

namespace EfficientFFA.Native.Expression
variable {α : Type*}

/-- Substitute 1+x for every semantic variable. Constants are unchanged. -/
def shift : Expression α → Expression α
  | .const c => .const c
  | .var a => .const 1 + .var a
  | .add e f => shift e + shift f
  | .mul e f => shift e * shift f
  | .neg e => -shift e

theorem value_shift {K : Type*} [Ring K] (e : Expression α) (x : α → K) :
    value x e.shift = value (fun a => 1+x a) e := by
  induction e <;> simp_all [shift, value]

/-- Actual sparse limb polynomial for the shifted interpretation 1+eval. -/
def compileShifted (B : ℤ) (n : ℕ) (e : Expression α) : Polynomial (α × Fin n) :=
  e.shift.compile B n

theorem compileShifted_eval (B : ℤ) (n : ℕ) (e : Expression α)
    (x : α × Fin n → ℤ) :
    Polynomial.eval (compileShifted B n e) x =
      value (fun a => ShiftedEncoding.value B (fun i => x (a,i))) e := by
  rw [compileShifted, compile_eval, value_shift]
  rfl

/-- Bounds are recomputed on the shifted polynomial, including its new terms. -/
theorem shifted_residual_bounds {r n : ℕ} (P : Parameters r) (hp : P.Positive)
    (e : Expression α) {x : α × Fin n → ℤ} (hx : Polynomial.Bounded P.B x) :
    -P.A (e.compileShifted P.B n) ≤ P.residual (e.compileShifted P.B n) x ∧
      P.residual (e.compileShifted P.B n) x ≤ P.C (e.compileShifted P.B n) :=
  P.residual_bounds hp _ hx

theorem shifted_auxCore_bounds {r n : ℕ} (P : Parameters r) (hp : P.Positive)
    (e : Expression α) {x : α × Fin n → ℤ} {u : ℤ}
    (hx : Polynomial.Bounded P.B x) (hu : 0 ≤ u ∧ u < P.Umax) (a : Fin r) :
    -P.Am (e.compileShifted P.B n) a ≤ P.auxCore (e.compileShifted P.B n) x u a ∧
      P.auxCore (e.compileShifted P.B n) x u a ≤ P.Cm (e.compileShifted P.B n) a :=
  P.auxCore_bounds hp _ hx hu a

/-- Correct bounded shifted inputs admit the explicit quotient witnesses. -/
theorem shifted_witnesses_accept {r n : ℕ} (P : Parameters r) (hp : P.Positive)
    (e : Expression α) (hw : P.WidthBounds (e.compileShifted P.B n))
    {x : α × Fin n → ℤ} (hx : Polynomial.Bounded P.B x)
    (he : value (fun a => ShiftedEncoding.value P.B (fun i => x (a,i))) e ≡ 0 [ZMOD P.q]) :
    P.Accepts (e.compileShifted P.B n) x
      (P.witnessU (e.compileShifted P.B n) x) (P.witnessV (e.compileShifted P.B n) x) :=
  P.witnesses_accept hp hw hx (by simpa only [compileShifted_eval] using he)

/-- Soundness and completeness for supplied shifted limb vectors. Validity
concerns the shifted polynomial; validity of the ordinary one is insufficient. -/
theorem shifted_accepts_iff {r n : ℕ} (P : Parameters r) (e : Expression α)
    (hp : P.Valid (e.compileShifted P.B n)) {x : α × Fin n → ℤ}
    (hx : Polynomial.Bounded P.B x) :
    (∃ u v, P.Accepts (e.compileShifted P.B n) x u v) ↔
      value (fun a => ShiftedEncoding.value P.B (fun i => x (a,i))) e ≡ 0 [ZMOD P.q] := by
  simpa only [compileShifted_eval] using P.accepts_iff (e.compileShifted P.B n) hp hx

/-- Native equations with bounded limbs representing the shifted semantic inputs.
No intermediate foreign-field normalization is introduced by the substitution. -/
def ShiftedChecks {r : ℕ} (P : Parameters r) (n q : ℕ)
    (e : Expression α) (values : α → ZMod q) : Prop :=
  ∃ x : α × Fin n → ℤ, Polynomial.Bounded P.B x ∧
    (∀ a, (ShiftedEncoding.value P.B (fun i => x (a,i)) : ZMod q) = values a) ∧
    ∃ u v, P.Accepts (e.compileShifted P.B n) x u v

theorem shifted_checks_sound {r n q : ℕ} (P : Parameters r) (hq : P.q = q)
    {e : Expression α} (hp : P.Valid (e.compileShifted P.B n)) {values : α → ZMod q}
    (hc : ShiftedChecks P n q e values) : value values e = 0 := by
  obtain ⟨x, hx, hr, u, v, ha⟩ := hc
  have h := (shifted_accepts_iff P e hp hx).mp ⟨u, v, ha⟩
  rw [hq, ← ZMod.intCast_eq_intCast_iff] at h
  simpa only [Int.cast_zero, cast_value, value_congr e hr] using h

theorem shifted_checks_complete {r n q : ℕ} [NeZero q] (P : Parameters r)
    (hq : P.q = q) {e : Expression α} (hp : P.Valid (e.compileShifted P.B n))
    (hcap : P.q ≤ P.B^n) {values : α → ZMod q} (he : value values e = 0) :
    ShiftedChecks P n q e values := by
  have hex : ∀ a, ∃ z : Limbs n, WellFormed P.B z ∧
      (ShiftedEncoding.value P.B z : ZMod q) = values a := by
    intro a
    obtain ⟨z, hz, hr⟩ := ShiftedEncoding.exists_representation hp.positive.radix
      hp.positive.foreign hcap (values a).val
    refine ⟨z, hz, ?_⟩
    rw [hq, ← ZMod.intCast_eq_intCast_iff] at hr
    simpa using hr
  choose z hz hr using hex
  let x : α × Fin n → ℤ := fun a => z a.1 a.2
  have hx : Polynomial.Bounded P.B x := fun a => hz a.1 a.2
  have hd : value (fun a => ShiftedEncoding.value P.B (fun i => x (a,i))) e ≡ 0 [ZMOD P.q] := by
    rw [hq, ← ZMod.intCast_eq_intCast_iff, Int.cast_zero, cast_value]
    exact (value_congr e hr).trans he
  exact ⟨x, hx, hr, _, _, shifted_witnesses_accept P hp.positive e hp.widths hx hd⟩

theorem shifted_checks_iff {r n q : ℕ} [NeZero q] (P : Parameters r) (hq : P.q = q)
    {e : Expression α} (hp : P.Valid (e.compileShifted P.B n)) (hcap : P.q ≤ P.B^n)
    (values : α → ZMod q) : ShiftedChecks P n q e values ↔ value values e = 0 :=
  ⟨shifted_checks_sound P hq hp, shifted_checks_complete P hq hp hcap⟩

end EfficientFFA.Native.Expression
