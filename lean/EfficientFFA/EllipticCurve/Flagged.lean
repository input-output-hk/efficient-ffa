import EfficientFFA.EllipticCurve.GroupLaw

namespace EfficientFFA.EllipticCurve

/-- The paper's Boolean infinity tag; coordinates are ignored when it is true. -/
structure Encoded (K : Type*) where
  coords : Coordinates K
  infinity : Bool
  deriving DecidableEq

namespace Curve
variable {K : Type*} [Field K] (C : Curve K)

def Valid (P : Encoded K) : Prop := P.infinity = false → C.OnCurve P.coords

def decode (P : Encoded K) (hP : C.Valid P) : C.Point :=
  if h : P.infinity = false then C.point P.coords (hP h) else 0

theorem decode_finite {P : Encoded K} (hP : C.Valid P) (h : P.infinity = false) :
    C.decode P hP = C.point P.coords (hP h) := by simp [decode, h]

theorem decode_infinity {P : Encoded K} (hP : C.Valid P) (h : P.infinity = true) :
    C.decode P hP = 0 := by simp [decode, h]

/-- fig:double: copy the infinity tag and enable the three equations only for finite inputs. -/
def DoubleAccepts (P R : Encoded K) (slope : K) : Prop :=
  R.infinity = P.infinity ∧ (P.infinity = false → DoubleChecks C P.coords R.coords slope)

/-- fig:incomplete-add, with its input preconditions kept separate. -/
def IncompleteAccepts (P Q R : Encoded K) (slope : K) : Prop :=
  R.infinity = false ∧ AddChecks P.coords Q.coords R.coords slope

variable [DecidableEq K]

theorem flagged_double_sound {P R : Encoded K} {slope : K}
    (hP : C.Valid P) (ha : C.DoubleAccepts P R slope) :
    ∃ hR : C.Valid R, C.decode R hR = C.decode P hP + C.decode P hP := by
  by_cases hp : P.infinity = false
  · obtain ⟨hR, he⟩ := C.doubling_sound (hP hp) (ha.2 hp)
    have hr : R.infinity = false := ha.1.trans hp
    refine ⟨fun _ => hR, ?_⟩
    simpa only [C.decode_finite _ hp, C.decode_finite _ hr] using he
  · have hr : R.infinity ≠ false := by simpa only [ha.1] using hp
    exact ⟨fun h => False.elim (hr h), by simp [decode, hp, hr]⟩

theorem flagged_double_complete {P : Encoded K} (hP : C.Valid P)
    (hden : P.infinity = false → 2*P.coords.y ≠ 0) :
    ∃ R slope, C.DoubleAccepts P R slope := by
  by_cases hp : P.infinity = false
  · obtain ⟨R, slope, hc, _⟩ := C.doubling_complete (hP hp) (hden hp)
    exact ⟨⟨R, false⟩, slope, hp.symm, fun _ => hc⟩
  · exact ⟨P, 0, rfl, fun h => False.elim (hp h)⟩

/-- fig:double is complete exactly when the finite input has nonzero tangent denominator. -/
theorem flagged_double_witnesses_iff {P : Encoded K} (hP : C.Valid P) :
    (∃ R slope, C.DoubleAccepts P R slope) ↔ (P.infinity = false → 2*P.coords.y ≠ 0) := by
  constructor
  · rintro ⟨R, slope, hc⟩ hp
    exact C.double_den_ne (hP hp) (hc.2 hp)
  · exact C.flagged_double_complete hP

theorem incomplete_sound {P Q R : Encoded K} {slope : K}
    (hP : C.Valid P) (hQ : C.Valid Q) (hp : P.infinity = false) (hq : Q.infinity = false)
    (hne : P.coords.x ≠ Q.coords.x) (ha : IncompleteAccepts P Q R slope) :
    ∃ hR : C.Valid R, C.decode R hR = C.decode P hP + C.decode Q hQ := by
  obtain ⟨hR, he⟩ := C.addition_sound (hP hp) (hQ hq) hne ha.2
  refine ⟨fun _ => hR, ?_⟩
  simpa only [C.decode_finite _ hp, C.decode_finite _ hq, C.decode_finite _ ha.1] using he

theorem incomplete_complete {P Q : Encoded K}
    (hP : C.Valid P) (hQ : C.Valid Q) (hp : P.infinity = false) (hq : Q.infinity = false)
    (hne : P.coords.x ≠ Q.coords.x) : ∃ R slope, IncompleteAccepts P Q R slope := by
  obtain ⟨R, slope, hc, _⟩ := C.addition_complete (hP hp) (hQ hq) hne
  exact ⟨⟨R, false⟩, slope, rfl, hc⟩

/-- The excluded finite inputs are exactly points whose double is the identity. -/
theorem double_eq_zero_iff {P : Coordinates K} (hP : C.OnCurve P) :
    C.point P hP + C.point P hP = 0 ↔ 2*P.y = 0 := by
  constructor
  · intro he
    by_contra hd
    obtain ⟨R, slope, _, hR, hg⟩ := C.doubling_complete hP hd
    exact C.point_ne_zero hR (hg.trans he)
  · intro hd
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp only [W, model, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
    linear_combination hd

/-- A no-order-two condition on the relevant group/subgroup suffices for fig:double.
It is local to the supplied point, so no global torsion axiom is needed. -/
theorem flagged_double_complete_of_no_two_torsion {P : Encoded K} (hP : C.Valid P)
    (hno : C.decode P hP + C.decode P hP = 0 → C.decode P hP = 0) :
    ∃ R slope, C.DoubleAccepts P R slope := by
  apply C.flagged_double_complete hP
  intro hp hz
  have hd := (C.double_eq_zero_iff (hP hp)).mpr hz
  have he : C.decode P hP = 0 := hno (by simpa only [C.decode_finite _ hp] using hd)
  exact C.point_ne_zero (hP hp) (by simpa only [C.decode_finite _ hp] using he)

end Curve

/-- Unordered coordinate-copy implications: both identity branches of
fig:complete-add enabled at once. The paper orders the branches; this
definition records why (see identity_copies_iff). When both inputs are
infinity, these copy constraints also copy ignored coordinates. -/
def IdentityCopies {K : Type*} (P Q R : Encoded K) : Prop :=
  (P.infinity = true → R = Q) ∧ (Q.infinity = true → R = P)

/-- Arbitrary distinct infinity encodings cannot simultaneously satisfy both copies. -/
theorem identity_copies_iff {K : Type*} {P Q : Encoded K}
    (hp : P.infinity = true) (hq : Q.infinity = true) :
    (∃ R, IdentityCopies P Q R) ↔ P = Q := by
  constructor
  · rintro ⟨R, hl, hr⟩
    exact (hr hq).symm.trans (hl hp)
  · rintro rfl
    exact ⟨P, fun _ => rfl, fun _ => rfl⟩

end EfficientFFA.EllipticCurve
