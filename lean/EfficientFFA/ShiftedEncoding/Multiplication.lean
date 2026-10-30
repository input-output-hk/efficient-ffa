import EfficientFFA.ShiftedEncoding.Multiplication.Completeness

namespace EfficientFFA.ShiftedEncoding.Multiplication.Parameters
variable {n r : ℕ} (P : Parameters n r)

/-- Acceptance is equivalent to multiplication of the shifted foreign values. -/
theorem accepts_iff_multiplication (hP : P.Valid) {x y z : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z) :
    (∃ u v, P.Accepts x y z u v) ↔
      value P.B x * value P.B y ≡ value P.B z [ZMOD P.q] := by
  constructor
  · rintro ⟨u, v, ha⟩
    exact P.multiplication_sound hP.positive hP.nowrap hx hy hz ha
  · exact P.multiplication_complete hP.positive hP.widths hx hy hz

/-- Capacity and witness widths suffice to construct an output and accepting witnesses. -/
theorem multiplication_exists (hP : P.Positive) (hw : P.WidthBounds)
    (hcap : P.q ≤ P.B ^ n) {x y : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts x y z u v := by
  obtain ⟨z, hz, he⟩ := exists_representation hP.radix hP.foreign hcap
    (value P.B x * value P.B y)
  exact ⟨z, P.witnessU x y z, P.witnessV x y z, hz,
    P.canonical_witnesses_accept hP hw hx hy hz he.symm⟩

end EfficientFFA.ShiftedEncoding.Multiplication.Parameters
