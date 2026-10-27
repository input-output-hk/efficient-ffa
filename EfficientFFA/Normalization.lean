import EfficientFFA.Normalization.Completeness
import EfficientFFA.Representation

namespace EfficientFFA.Normalization.Parameters
variable {n r : ℕ} (P : Parameters n r)

/-- Normalization checks are equivalent to preservation of the foreign residue. -/
theorem accepts_iff_normalization (hP : P.Valid) {x z : Limbs n}
    (hx : P.InputBounded x) (hz : WellFormed P.B z) :
    (∃ u v, P.Accepts x z u v) ↔ eval P.B x ≡ eval P.B z [ZMOD P.q] := by
  constructor
  · rintro ⟨u, v, ha⟩
    exact P.normalization_sound hP.positive hP.nowrap hx hz ha
  · exact P.normalization_complete hP.positive hP.widths hx hz

/-- Capacity plus witness widths guarantees an actual canonical output and witnesses. -/
theorem normalization_exists (hP : P.Positive) (hw : P.WidthBounds)
    (hcap : P.q ≤ P.B ^ n) {x : Limbs n} (hx : P.InputBounded x) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts x z u v ∧ eval P.B z = eval P.B x % P.q := by
  obtain ⟨z, hz, he⟩ := exists_canonical_limbs hP.radix hP.foreign n hcap (eval P.B x)
  have hm : eval P.B x ≡ eval P.B z [ZMOD P.q] := by simp [Int.ModEq, he]
  exact ⟨z, P.witnessU x z, P.witnessV x z, hz,
    P.canonical_witnesses_accept hP hw hx hz hm, he⟩

/-- Native checks are insensitive to replacing a signed input by its stored residues. -/
theorem nativeResidual_congr {stored x : Limbs n}
    (hs : LazyArithmetic.Represents P.p stored x) (z : Limbs n) (u : ℤ) :
    P.nativeResidual stored z u ≡ P.nativeResidual x z u [ZMOD P.p] := by
  have hsum : (∑ i, P.singleCoeff i * stored i) ≡
      (∑ i, P.singleCoeff i * x i) [ZMOD P.p] :=
    Int.ModEq.sum fun i _ => (Int.ModEq.refl _).mul (hs i)
  exact (hsum.sub (Int.ModEq.refl _)).sub (Int.ModEq.refl _)

theorem auxResidual_congr {stored x : Limbs n}
    (hs : LazyArithmetic.Represents P.p stored x) (z : Limbs n) (u v : ℤ) (a : Fin r) :
    P.auxResidual stored z u v a ≡ P.auxResidual x z u v a [ZMOD P.p] := by
  have hsum : (∑ i, (P.singleCoeff i % P.M a) * stored i) ≡
      (∑ i, (P.singleCoeff i % P.M a) * x i) [ZMOD P.p] :=
    Int.ModEq.sum fun i _ => (Int.ModEq.refl _).mul (hs i)
  exact (((hsum.sub (Int.ModEq.refl _)).sub (Int.ModEq.refl _)).sub
    (Int.ModEq.refl _)).sub (Int.ModEq.refl _)

theorem accepts_of_rep {stored x z : Limbs n} {u : ℤ} {v : Fin r → ℤ}
    (hs : LazyArithmetic.Represents P.p stored x) (ha : P.Accepts stored z u v) :
    P.Accepts x z u v := by
  refine ⟨ha.u_range, ha.v_range, ?_, ?_⟩
  · exact (P.nativeResidual_congr hs z u).symm.trans ha.native
  · intro a
    exact (P.auxResidual_congr hs z u (v a) a).symm.trans (ha.auxiliary a)

/-- Soundness for checks on stored residues, using independently tracked signed bounds. -/
theorem stored_normalization_sound (hP : P.Positive) (hnw : P.NoWrap)
    {stored x z : Limbs n} {u : ℤ} {v : Fin r → ℤ}
    (hs : LazyArithmetic.Represents P.p stored x)
    (hx : P.InputBounded x) (hz : WellFormed P.B z) (ha : P.Accepts stored z u v) :
    eval P.B x ≡ eval P.B z [ZMOD P.q] :=
  P.normalization_sound hP hnw hx hz (P.accepts_of_rep hs ha)

theorem stored_normalization_exists (hP : P.Positive) (hw : P.WidthBounds)
    (hcap : P.q ≤ P.B ^ n) {stored x : Limbs n}
    (hs : LazyArithmetic.Represents P.p stored x) (hx : P.InputBounded x) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts stored z u v ∧ eval P.B z = eval P.B x % P.q := by
  obtain ⟨z, u, v, hz, ha, he⟩ := P.normalization_exists hP hw hcap hx
  exact ⟨z, u, v, hz, P.accepts_of_rep (fun i => (hs i).symm) ha, he⟩

/-- Compose a native subtraction with normalization of its tracked integer result. -/
theorem subtraction_normalization_sound (hP : P.Positive) (hnw : P.NoWrap)
    {sx sy stored x y z : Limbs n} {u : ℤ} {v : Fin r → ℤ}
    (hsx : LazyArithmetic.Represents P.p sx x) (hsy : LazyArithmetic.Represents P.p sy y)
    (hsub : ∀ i, stored i ≡ sx i - sy i [ZMOD P.p])
    (hb : P.InputBounded (fun i => x i - y i)) (hz : WellFormed P.B z)
    (ha : P.Accepts stored z u v) :
    eval P.B x - eval P.B y ≡ eval P.B z [ZMOD P.q] := by
  simpa only [eval_sub] using P.stored_normalization_sound hP hnw
    (LazyArithmetic.represents_sub hsx hsy hsub) hb hz ha

end EfficientFFA.Normalization.Parameters
