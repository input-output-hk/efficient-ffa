import EfficientFFA.EllipticCurve.Flagged

namespace EfficientFFA.EllipticCurve.Curve
variable {K : Type*} [Field K] (C : Curve K)

/-- A branch-ordered complete addition contract. Identity branches take precedence;
inverse finite inputs precede doubling. This is the ordered if/else of
fig:complete-add, not a conjunction of overlapping coordinate-copy implications. -/
inductive CompleteAccepts (P Q R : Encoded K) : Prop
  | left (hp : P.infinity = true) (hout : R = Q)
  | right (hp : P.infinity = false) (hq : Q.infinity = true) (hout : R = P)
  | inverse (hp : P.infinity = false) (hq : Q.infinity = false)
      (hx : P.coords.x = Q.coords.x) (hy : P.coords.y = -Q.coords.y) (hr : R.infinity = true)
  | double (hp : P.infinity = false) (hq : Q.infinity = false)
      (he : P.coords = Q.coords) (slope : K) (hc : C.DoubleAccepts P R slope)
  | distinct (hp : P.infinity = false) (hq : Q.infinity = false)
      (hne : P.coords.x ≠ Q.coords.x) (slope : K) (hc : IncompleteAccepts P Q R slope)

variable [DecidableEq K]

theorem complete_sound {P Q R : Encoded K} (hP : C.Valid P) (hQ : C.Valid Q)
    (ha : C.CompleteAccepts P Q R) :
    ∃ hR : C.Valid R, C.decode R hR = C.decode P hP + C.decode Q hQ := by
  cases ha with
  | left hp he =>
    subst R
    refine ⟨hQ, ?_⟩
    rw [C.decode_infinity hP hp, zero_add]
  | right hp hq he =>
    subst R
    refine ⟨hP, ?_⟩
    rw [C.decode_infinity hQ hq, add_zero]
  | inverse hp hq hx hy hr =>
    have hR : C.Valid R := by intro h; simp_all
    refine ⟨hR, ?_⟩
    rw [C.decode_infinity hR hr, C.decode_finite hP hp, C.decode_finite hQ hq]
    symm
    apply WeierstrassCurve.Affine.Point.add_of_Y_eq hx
    simpa [W, model, WeierstrassCurve.Affine.negY] using hy
  | double hp hq he slope hc =>
    have heq : P = Q := by cases P; cases Q; simp_all
    subst Q
    exact C.flagged_double_sound hP hc
  | distinct hp hq hne slope hc =>
    exact C.incomplete_sound hP hQ hp hq hne hc

/-- Completeness for every valid pair, including infinity and order-two points. -/
theorem complete_exists {P Q : Encoded K} (hP : C.Valid P) (hQ : C.Valid Q) :
    ∃ R, C.CompleteAccepts P Q R := by
  by_cases hp : P.infinity = true
  · exact ⟨Q, .left hp rfl⟩
  have hp' : P.infinity = false := by cases h : P.infinity <;> simp_all
  by_cases hq : Q.infinity = true
  · exact ⟨P, .right hp' hq rfl⟩
  have hq' : Q.infinity = false := by cases h : Q.infinity <;> simp_all
  by_cases hi : P.coords.x = Q.coords.x ∧ P.coords.y = -Q.coords.y
  · exact ⟨⟨P.coords, true⟩, .inverse hp' hq' hi.1 hi.2 rfl⟩
  by_cases hx : P.coords.x = Q.coords.x
  · have hy : P.coords.y = Q.coords.y :=
      (C.same_x_cases (hP hp') (hQ hq') hx).resolve_right (fun h => hi ⟨hx, h⟩)
    have he : P.coords = Q.coords := by
      rcases P with ⟨⟨px, py⟩, pi⟩
      rcases Q with ⟨⟨qx, qy⟩, qi⟩
      simp_all
    have hd : 2*P.coords.y ≠ 0 := by
      intro hz
      apply hi
      refine ⟨hx, ?_⟩
      rw [← hy]
      linear_combination hz
    obtain ⟨R, slope, hc⟩ := C.flagged_double_complete hP (fun _ => hd)
    exact ⟨R, .double hp' hq' he slope hc⟩
  · obtain ⟨R, slope, hc⟩ := C.incomplete_complete hP hQ hp' hq' hx
    exact ⟨R, .distinct hp' hq' hx slope hc⟩

theorem complete_correct {P Q : Encoded K} (hP : C.Valid P) (hQ : C.Valid Q) :
    ∃ R, C.CompleteAccepts P Q R ∧
      ∃ hR : C.Valid R, C.decode R hR = C.decode P hP + C.decode Q hQ := by
  obtain ⟨R, ha⟩ := C.complete_exists hP hQ
  exact ⟨R, ha, C.complete_sound hP hQ ha⟩

end EfficientFFA.EllipticCurve.Curve
