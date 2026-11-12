import EfficientFFA.ShiftedEncoding.Expression
import EfficientFFA.Native.EllipticCurve

namespace EfficientFFA.Native
open EllipticCurve

/-- Arithmetic certificates for EC identities under the shifted interpretation.
The additional upper capacity bound is required only for unique-zero theorems. -/
structure ShiftedECEncoding {q : ℕ} [Fact q.Prime] (C : Curve (ZMod q)) (n r : ℕ) where
  params : Parameters r
  foreign_eq : params.q = q
  capacity : params.q ≤ params.B^n
  valid : ∀ k : GateKind,
    params.Valid ((k.expression C.a.val C.b.val).compileShifted params.B n)

namespace ShiftedECEncoding
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ShiftedECEncoding C n r)

/-- Actual native-modulus checks on shifted limb representations. -/
def Check (k : GateKind) (values : Fin 8 → ZMod q) : Prop :=
  Expression.ShiftedChecks E.params n q (k.expression C.a.val C.b.val) values

theorem check_iff (k : GateKind) (values : Fin 8 → ZMod q) :
    E.Check k values ↔ (k.expression C.a.val C.b.val).value values = 0 :=
  Expression.shifted_checks_iff E.params E.foreign_eq (E.valid k) E.capacity values

/-- Ordinary and shifted witnesses encode the same coordinate identity, with
separate numerical certificates and possibly different limb counts/moduli. -/
theorem check_iff_ordinary {n' r' : ℕ} (O : ECEncoding C n' r')
    (k : GateKind) (values : Fin 8 → ZMod q) : E.Check k values ↔ O.Check k values :=
  (E.check_iff k values).trans (O.check_iff k values).symm

/-- Shifted arithmetic alone does not imply this capacity condition. -/
theorem unique_zero (hcap : E.params.B^n < 2*E.params.q) :
    ∃! x : Limbs n, WellFormed E.params.B x ∧
      ShiftedEncoding.value E.params.B x ≡ 0 [ZMOD E.params.q] :=
  ShiftedEncoding.exists_unique_zero (E.valid .equal).positive.radix
    (E.valid .equal).positive.foreign E.capacity hcap

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

/-- Reuse the coordinate/group proof after discharging the shifted identities. -/
theorem addition_sound {P Q R : Coordinates (ZMod q)} {slope : ZMod q}
    (hP : C.OnCurve P) (hQ : C.OnCurve Q) (hne : P.x ≠ Q.x)
    (hc : E.Add P Q R slope) :
    ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point Q hQ :=
  C.addition_sound hP hQ hne ((E.add_iff P Q R slope).mp hc)

theorem addition_complete {P Q : Coordinates (ZMod q)}
    (hP : C.OnCurve P) (hQ : C.OnCurve Q) (hne : P.x ≠ Q.x) :
    ∃ R slope, E.Add P Q R slope ∧
      ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point Q hQ := by
  obtain ⟨R, slope, hc, hR⟩ := C.addition_complete hP hQ hne
  exact ⟨R, slope, (E.add_iff P Q R slope).mpr hc, hR⟩

/-- No additional denominator guard is needed for doubling soundness. -/
theorem doubling_sound {P R : Coordinates (ZMod q)} {slope : ZMod q}
    (hP : C.OnCurve P) (hc : E.Double P R slope) :
    ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point P hP :=
  C.doubling_sound hP ((E.double_iff P R slope).mp hc)

theorem doubling_complete {P : Coordinates (ZMod q)}
    (hP : C.OnCurve P) (hden : 2*P.y ≠ 0) :
    ∃ R slope, E.Double P R slope ∧
      ∃ hR : C.OnCurve R, C.point R hR = C.point P hP + C.point P hP := by
  obtain ⟨R, slope, hc, hR⟩ := C.doubling_complete hP hden
  exact ⟨R, slope, (E.double_iff P R slope).mpr hc, hR⟩

theorem doubling_witnesses_iff {P : Coordinates (ZMod q)} (hP : C.OnCurve P) :
    (∃ R slope, E.Double P R slope) ↔ 2*P.y ≠ 0 := by
  simp only [E.double_iff]
  exact C.doubling_witnesses_iff hP

end ShiftedECEncoding
end EfficientFFA.Native
