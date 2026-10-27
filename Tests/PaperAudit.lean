import EfficientFFA
import Tests.Tables

namespace EfficientFFA.Tests.PaperAudit
open EllipticCurve

/-- Figure 3 Step 3 conflicts with Step 5 when its inverse predicate is the
coordinate-only comparison explicitly described in Section 4.4.2. This works
for any finite Q; the ignored coordinates of infinity can be chosen as -Q. -/
theorem single_infinity_literal_conflict {K : Type*} [Field K]
    (Q : Encoded K) (hq : Q.infinity = false) :
    let P : Encoded K := ⟨Curve.opposite Q.coords, true⟩
    ¬ ∃ R : Encoded K,
      (P.infinity = true → R = Q) ∧
      ((P.coords.x = Q.coords.x ∧ P.coords.y = -Q.coords.y) → R.infinity = true) := by
  dsimp
  rintro ⟨R, hcopy, hinverse⟩
  have he : R = Q := hcopy rfl
  have ht : R.infinity = true := hinverse ⟨rfl, rfl⟩
  rw [he, hq] at ht
  cases ht

private def finiteP : Encoded (ZMod 17) := finiteEncoding Tables.base17
private def infinity : Encoded (ZMod 17) := ⟨Curve.opposite Tables.base17, true⟩

-- Both encodings are valid under the paper's arbitrary-coordinate infinity convention.
example : Tables.C17.Valid finiteP := fun _ => Tables.base17_on
example : Tables.C17.Valid infinity := by
  intro h
  cases h

example : ¬ ∃ R : Encoded (ZMod 17),
    (infinity.infinity = true → R = finiteP) ∧
    ((infinity.coords.x = finiteP.coords.x ∧ infinity.coords.y = -finiteP.coords.y) →
      R.infinity = true) := single_infinity_literal_conflict finiteP rfl

-- The already documented ordered refinement admits the required output Q.
example : Tables.C17.CompleteAccepts infinity finiteP finiteP := .left rfl rfl

end EfficientFFA.Tests.PaperAudit
