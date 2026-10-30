import EfficientFFA.Multiplication.Completeness

namespace EfficientFFA.Multiplication.Parameters
variable {n r : ℕ} (P : Parameters n r)

/-- The complete multiplication contract for already bounded input/output limbs. -/
theorem accepts_iff_multiplication (hP : P.Valid) {x y z : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z) :
    (∃ u v, P.Accepts x y z u v) ↔
      eval P.B x * eval P.B y ≡ eval P.B z [ZMOD P.q] := by
  constructor
  · rintro ⟨u, v, hacc⟩
    exact P.multiplication_sound hP.positive hP.nowrap hx hy hz hacc
  · exact P.multiplication_complete hP.positive hP.widths hx hy hz

/-- Canonical equality requires an additional output-value range, beyond limb ranges. -/
theorem canonical_output (hP : P.Positive) (hnw : P.NoWrap)
    {x y z : Limbs n} {u : ℤ} {v : Fin r → ℤ}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hacc : P.Accepts x y z u v)
    (hcanon : 0 ≤ eval P.B z ∧ eval P.B z < P.q) :
    eval P.B z = (eval P.B x * eval P.B y) % P.q := by
  have hm := P.multiplication_sound hP hnw hx hy hz hacc
  exact (Int.emod_eq_of_lt hcanon.1 hcanon.2).symm.trans hm.symm

end EfficientFFA.Multiplication.Parameters
