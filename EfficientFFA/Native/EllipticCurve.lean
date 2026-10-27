import EfficientFFA.Native.Activation
import EfficientFFA.EllipticCurve.Complete

namespace EfficientFFA.Native
open EllipticCurve

/-- Equations (6)--(9), plus square linkage, copies and a nonzero certificate. -/
inductive GateKind where
  | curve | square | slopePlus | slopeMinus | tangent | xout | equal | negative | inverse
  deriving DecidableEq, Fintype

namespace GateKind
open Expression

def expression (a b : ℤ) : GateKind → Expression (Fin 8)
  | .curve => .var 1 * .var 1 - .var 0 * .var 7 - .const a * .var 0 - .const b
  | .square => .var 0 * .var 0 - .var 7
  | .slopePlus => .var 3 - .var 1 - (.var 2 - .var 0) * .var 6
  | .slopeMinus => -(.var 3) - .var 1 - (.var 2 - .var 0) * .var 6
  | .tangent => 3 * (.var 0 * .var 0) + .const a - 2 * .var 1 * .var 6
  | .xout => .var 0 + .var 2 + .var 4 - .var 6 * .var 6
  | .equal => .var 0 - .var 2
  | .negative => .var 0 + .var 2
  | .inverse => (.var 0 - .var 2) * .var 6 - 1
end GateKind

/-- All numerical obligations are explicit and independently checkable. -/
structure ECEncoding {q : ℕ} [Fact q.Prime] (C : Curve (ZMod q)) (n r : ℕ) where
  params : Parameters r
  foreign_eq : params.q = q
  capacity : params.q ≤ params.B^n
  valid : ∀ k : GateKind, params.Valid ((k.expression C.a.val C.b.val).compile params.B n)
  native_gt_one : 1 < params.p

namespace ECEncoding
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

/-- Enabled gate checks include a native activation bit equal to one.
Inactive branch equations may use Parameters.activated_zero. -/
def Check (k : GateKind) (values : Fin 8 → ZMod q) : Prop :=
  ∃ x : Fin 8 × Fin n → ℤ, Polynomial.Bounded E.params.B x ∧
    (∀ a, (EfficientFFA.eval E.params.B (fun i => x (a,i)) : ZMod q) = values a) ∧
    ∃ u v, E.params.Activated ((k.expression C.a.val C.b.val).compile E.params.B n) x 1 u v

theorem check_checks (k : GateKind) (values : Fin 8 → ZMod q) :
    E.Check k values ↔ Expression.Checks E.params n q (k.expression C.a.val C.b.val) values := by
  constructor
  · rintro ⟨x, hx, hr, u, v, ha⟩
    exact ⟨x, hx, hr, u, v, ha.u_range, ha.v_range, by simpa using ha.native,
      fun a => by simpa using ha.auxiliary a⟩
  · rintro ⟨x, hx, hr, u, v, ha⟩
    exact ⟨x, hx, hr, u, v, E.params.activated_one E.native_gt_one ha⟩

theorem check_iff (k : GateKind) (values : Fin 8 → ZMod q) :
    E.Check k values ↔ (k.expression C.a.val C.b.val).value values = 0 :=
  (E.check_checks k values).trans
    (Expression.checks_iff E.params E.foreign_eq (E.valid k) E.capacity values)

def Equal (x y : ZMod q) := E.Check .equal ![x,0,y,0,0,0,0,0]
def Negative (x y : ZMod q) := E.Check .negative ![x,0,y,0,0,0,0,0]
def Distinct (x y : ZMod q) := ∃ inv, E.Check .inverse ![x,0,y,0,0,0,inv,0]

theorem equal_iff (x y : ZMod q) : E.Equal x y ↔ x = y := by
  rw [Equal, E.check_iff]
  simp [GateKind.expression, Expression.value, sub_eq_zero]

theorem negative_iff (x y : ZMod q) : E.Negative x y ↔ x = -y := by
  rw [Negative, E.check_iff]
  simp [GateKind.expression, Expression.value, eq_neg_iff_add_eq_zero]

theorem distinct_iff (x y : ZMod q) : E.Distinct x y ↔ x ≠ y := by
  simp only [Distinct, E.check_iff]
  simp [GateKind.expression, Expression.value, sub_eq_zero]
  constructor
  · rintro ⟨inv, hi⟩ he
    simp [he] at hi
  · intro he
    exact ⟨(x-y)⁻¹, mul_inv_cancel₀ (sub_ne_zero.mpr he)⟩

def Copy (P Q : Coordinates (ZMod q)) := E.Equal P.x Q.x ∧ E.Equal P.y Q.y

theorem copy_iff (P Q : Coordinates (ZMod q)) : E.Copy P Q ↔ P = Q := by
  rw [Copy, E.equal_iff, E.equal_iff]
  cases P; cases Q
  simp

/-- The auxiliary square is checked, not an independent assumption. -/
def OnCurve (P : Coordinates (ZMod q)) := ∃ z,
  E.Check .square ![P.x,P.y,0,0,0,0,0,z] ∧ E.Check .curve ![P.x,P.y,0,0,0,0,0,z]

theorem onCurve_iff (P : Coordinates (ZMod q)) : E.OnCurve P ↔ C.OnCurve P := by
  simp only [OnCurve, E.check_iff]
  simp [GateKind.expression, Expression.value]
  constructor
  · rintro ⟨z, hz, hc⟩
    dsimp [Curve.OnCurve]
    linear_combination hc - P.x * hz
  · intro hc
    refine ⟨P.x^2, by ring, ?_⟩
    dsimp [Curve.OnCurve] at hc
    linear_combination hc

def Add (P Q R : Coordinates (ZMod q)) (s : ZMod q) :=
  E.Check .slopePlus ![P.x,P.y,Q.x,Q.y,R.x,R.y,s,0] ∧
  E.Check .xout ![P.x,P.y,Q.x,Q.y,R.x,R.y,s,0] ∧
  E.Check .slopeMinus ![P.x,P.y,R.x,R.y,0,0,s,0]

theorem add_iff (P Q R : Coordinates (ZMod q)) (s : ZMod q) :
    E.Add P Q R s ↔ AddChecks P Q R s := by
  simp only [Add, E.check_iff]
  simp [GateKind.expression, Expression.value]
  constructor
  · intro h
    exact ⟨by simpa [mul_comm] using h.1, by simpa [pow_two] using h.2.1, by simpa [mul_comm] using h.2.2⟩
  · intro h
    exact ⟨by simpa [mul_comm] using h.slope_eq, by simpa [pow_two] using h.x_eq, by simpa [mul_comm] using h.y_eq⟩

def Double (P R : Coordinates (ZMod q)) (s : ZMod q) :=
  E.Check .tangent ![P.x,P.y,P.x,P.y,R.x,R.y,s,0] ∧
  E.Check .xout ![P.x,P.y,P.x,P.y,R.x,R.y,s,0] ∧
  E.Check .slopeMinus ![P.x,P.y,R.x,R.y,0,0,s,0]

theorem double_iff (P R : Coordinates (ZMod q)) (s : ZMod q) :
    E.Double P R s ↔ DoubleChecks C P R s := by
  simp only [Double, E.check_iff]
  simp [GateKind.expression, Expression.value]
  constructor
  · intro h
    exact ⟨by simpa [pow_two] using h.1, by simpa [pow_two, two_mul] using h.2.1, by simpa [mul_comm] using h.2.2⟩
  · intro h
    exact ⟨by simpa [pow_two] using h.slope_eq, by simpa [pow_two, two_mul] using h.x_eq, by simpa [mul_comm] using h.y_eq⟩

end ECEncoding
end EfficientFFA.Native
