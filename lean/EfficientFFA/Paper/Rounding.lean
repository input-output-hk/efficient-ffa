import EfficientFFA.Multiplication.Definitions
import EfficientFFA.Normalization.Definitions
import EfficientFFA.Native.Gate

namespace EfficientFFA.Paper

/-- For a positive divisor, truncation is an upper bound for floor division. -/
theorem floor_le_trunc (a : ℤ) {b : ℤ} (hb : 0 < b) : a / b ≤ a.tdiv b := by
  rw [Int.tdiv_eq_ediv, Int.sign_eq_one_of_pos hb]
  split <;> omega

/-- A truncated negative lower endpoint equals the ceiling endpoint used by
the paper and Lean. -/
theorem lower_trunc_eq {A : ℤ} (hA : 0 ≤ A) (q : ℤ) :
    (-A).tdiv q = -(A / q) := by
  rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg hA]

/-- A width chosen from a truncated upper endpoint also contains the floor interval.
No statement about increasing the width while preserving no-wrap is made. -/
theorem floor_width_of_trunc {C m lo width : ℤ} (hm : 0 < m)
    (h : C.tdiv m - lo < width) : C / m - lo < width := by
  have := floor_le_trunc C hm
  omega

/-- Compatibility with the actual multiplication parameters, at unchanged widths. -/
theorem multiplication_widths_of_trunc {n r : ℕ} (P : Multiplication.Parameters n r)
    (hp : P.Positive)
    (hu : P.C.tdiv P.q - P.kmin < P.Umax)
    (hv : ∀ a, (P.Cm a).tdiv (P.M a) - P.lmin a < P.Vmax a) : P.WidthBounds :=
  ⟨floor_width_of_trunc hp.foreign hu,
    fun a => floor_width_of_trunc (hp.auxiliary a) (hv a)⟩

theorem normalization_widths_of_trunc {n r : ℕ} (P : Normalization.Parameters n r)
    (hp : P.Positive)
    (hu : P.C.tdiv P.q - P.kmin < P.Umax)
    (hv : ∀ a, (P.Cm a).tdiv (P.M a) - P.lmin a < P.Vmax a) : P.WidthBounds :=
  ⟨floor_width_of_trunc hp.foreign hu,
    fun a => floor_width_of_trunc (hp.auxiliary a) (hv a)⟩

theorem native_widths_of_trunc {r : ℕ} {α : Type*} (P : Native.Parameters r)
    (e : Native.Polynomial α) (hp : P.Positive)
    (hu : (P.C e).tdiv P.q - P.kmin e < P.Umax)
    (hv : ∀ a, (P.Cm e a).tdiv (P.M a) - P.lmin e a < P.Vmax a) : P.WidthBounds e :=
  ⟨floor_width_of_trunc hp.foreign hu,
    fun a => floor_width_of_trunc (hp.auxiliary a) (hv a)⟩

/-- Soundness/completeness conditions at the chosen source-style widths.
The no-wrap proof must concern these very widths, not narrower ones. -/
theorem multiplication_valid_of_trunc {n r : ℕ} (P : Multiplication.Parameters n r)
    (hp : P.Positive)
    (hu : P.C.tdiv P.q - P.kmin < P.Umax)
    (hv : ∀ a, (P.Cm a).tdiv (P.M a) - P.lmin a < P.Vmax a)
    (hn : P.NoWrap) : P.Valid :=
  ⟨hp, multiplication_widths_of_trunc P hp hu hv, hn⟩

theorem normalization_valid_of_trunc {n r : ℕ} (P : Normalization.Parameters n r)
    (hp : P.Positive)
    (hu : P.C.tdiv P.q - P.kmin < P.Umax)
    (hv : ∀ a, (P.Cm a).tdiv (P.M a) - P.lmin a < P.Vmax a)
    (hn : P.NoWrap) : P.Valid :=
  ⟨hp, normalization_widths_of_trunc P hp hu hv, hn⟩

theorem native_valid_of_trunc {r : ℕ} {α : Type*} (P : Native.Parameters r)
    (e : Native.Polynomial α) (hp : P.Positive)
    (hu : (P.C e).tdiv P.q - P.kmin e < P.Umax)
    (hv : ∀ a, (P.Cm e a).tdiv (P.M a) - P.lmin e a < P.Vmax a)
    (hn : P.NoWrap e) : P.Valid e :=
  ⟨hp, native_widths_of_trunc P e hp hu hv, hn⟩

end EfficientFFA.Paper
