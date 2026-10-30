import EfficientFFA.Multiplication
import EfficientFFA.Normalization

namespace EfficientFFA.Division

/-- Inversion exists precisely for units, expressed by a Bézout certificate. -/
theorem inverse_exists_iff_coprime (q a : ℤ) :
    (∃ b : ℤ, a * b ≡ 1 [ZMOD q]) ↔ IsCoprime a q := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hb
    exact ⟨b, c, by nlinarith⟩
  · rintro ⟨b, c, hc⟩
    refine ⟨b, Int.modEq_iff_dvd.mpr ⟨c, ?_⟩⟩
    nlinarith

/-- A multiplication constraint is division only when the divisor is invertible. -/
theorem division_iff {q a b inv z : ℤ} (hi : b * inv ≡ 1 [ZMOD q]) :
    b * z ≡ a [ZMOD q] ↔ z ≡ a * inv [ZMOD q] := by
  constructor
  · intro hm
    calc
      z ≡ (b * inv) * z [ZMOD q] := by simpa using (hi.mul (Int.ModEq.refl z)).symm
      _ ≡ a * inv [ZMOD q] := by
        convert hm.mul (Int.ModEq.refl inv) using 1
        ring
  · intro hm
    calc
      b * z ≡ b * (a * inv) [ZMOD q] := (Int.ModEq.refl b).mul hm
      _ ≡ a [ZMOD q] := by
        convert hi.mul (Int.ModEq.refl a) using 1 <;> ring

/-- Over a prime modulus, invertibility is equivalent to nonzero residue. -/
theorem prime_inverse_iff (q : ℕ) (hq : q.Prime) (a : ℤ) :
    (∃ b : ℤ, a * b ≡ 1 [ZMOD (q : ℤ)]) ↔ ¬ a ≡ 0 [ZMOD (q : ℤ)] := by
  letI : Fact q.Prime := ⟨hq⟩
  constructor
  · rintro ⟨b, hb⟩ ha
    have hb' := (ZMod.intCast_eq_intCast_iff (a*b) 1 q).mpr hb
    have ha' := (ZMod.intCast_eq_intCast_iff a 0 q).mpr ha
    norm_num only [Int.cast_mul, Int.cast_one, Int.cast_zero] at hb' ha'
    rw [ha', zero_mul] at hb'
    exact zero_ne_one hb'
  · intro ha
    have ha' : (a : ZMod q) ≠ 0 := by
      intro hzero
      apply ha
      exact (ZMod.intCast_eq_intCast_iff a 0 q).mp (by simpa using hzero)
    refine ⟨((a : ZMod q)⁻¹).cast, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ q).mp
    simp only [Int.cast_mul, Int.cast_one, ZMod.intCast_zmod_cast]
    exact mul_inv_cancel₀ ha'

/-- Inverse-of-difference witnesses characterize disequality for prime q. -/
theorem prime_disequality_iff (q : ℕ) (hq : q.Prime) (a b : ℤ) :
    (∃ inv : ℤ, (a-b) * inv ≡ 1 [ZMOD (q : ℤ)]) ↔ ¬ a ≡ b [ZMOD (q : ℤ)] := by
  rw [prime_inverse_iff q hq]
  simp only [Int.ModEq, Int.zero_emod, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]

/-- Division expressed by the checked multiplication encoding. -/
theorem encoded_division_iff {n r : ℕ} (P : Multiplication.Parameters n r)
    (hP : P.Valid) {a b z : Limbs n} {inv : ℤ}
    (ha : WellFormed P.B a) (hb : WellFormed P.B b) (hz : WellFormed P.B z)
    (hi : eval P.B b * inv ≡ 1 [ZMOD P.q]) :
    (∃ u v, P.Accepts b z a u v) ↔ eval P.B z ≡ eval P.B a * inv [ZMOD P.q] :=
  (P.accepts_iff_multiplication hP hb hz ha).trans (division_iff hi)

/-- Inversion expressed by multiplication against a representation of one. -/
theorem encoded_inverse_iff {n r : ℕ} (P : Multiplication.Parameters n r)
    (hP : P.Valid) {x inv one : Limbs n}
    (hx : WellFormed P.B x) (hi : WellFormed P.B inv) (ho : WellFormed P.B one)
    (hone : eval P.B one = 1) :
    (∃ u v, P.Accepts x inv one u v) ↔ eval P.B x * eval P.B inv ≡ 1 [ZMOD P.q] := by
  simpa only [hone] using P.accepts_iff_multiplication hP hx hi ho

end EfficientFFA.Division
