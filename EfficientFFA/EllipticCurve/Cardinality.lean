import EfficientFFA.EllipticCurve.Affine

namespace EfficientFFA.EllipticCurve.Curve
variable {K : Type*} [Field K] (C : Curve K)

/-- The actual curve group consists of its affine solutions plus one infinity point. -/
def pointEquiv : C.Point ≃ Option {xy : K × K // C.OnCurve ⟨xy.1, xy.2⟩} where
  toFun g := match g with
    | .zero => none
    | .some x y h => some ⟨(x,y), (C.equation_iff ⟨x,y⟩).mp h.1⟩
  invFun g := match g with
    | none => .zero
    | some xy => C.point ⟨xy.val.1, xy.val.2⟩ xy.property
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g with
    | none => rfl
    | some xy => cases xy; rfl

/-- A finite enumeration obtained from affine field pairs, not a cardinality axiom. -/
abbrev pointFintype [Fintype K] [DecidableEq K] : Fintype C.Point := by
  letI : DecidablePred (fun xy : K × K => C.OnCurve ⟨xy.1,xy.2⟩) :=
    fun xy => inferInstanceAs (Decidable (xy.2^2 = xy.1^3+C.a*xy.1+C.b))
  exact Fintype.ofEquiv _ C.pointEquiv.symm

theorem natCard_points [Finite K] :
    Nat.card C.Point = Nat.card {xy : K × K // C.OnCurve ⟨xy.1,xy.2⟩} + 1 := by
  classical
  letI := Fintype.ofFinite K
  rw [Nat.card_congr C.pointEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

end EfficientFFA.EllipticCurve.Curve
