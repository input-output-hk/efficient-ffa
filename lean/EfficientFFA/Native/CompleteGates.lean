import EfficientFFA.Native.SharedGate

namespace EfficientFFA.Native.ECEncoding
open EllipticCurve
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

theorem zero_limbs_bounded : WellFormed E.params.B (0 : Limbs n) := by
  intro i
  exact ⟨by simp, (E.valid .equal).positive.radix⟩

def EqGate (a b : Limbs n) (s : ℤ) := E.FixedGate .equal ![a,0,b,0,0,0,0,0] s
def NegGate (a b : Limbs n) (s : ℤ) := E.FixedGate .negative ![a,0,b,0,0,0,0,0] s
def InvGate (a b inv : Limbs n) (s : ℤ) := E.FixedGate .inverse ![a,0,b,0,0,0,inv,0] s

@[simp] theorem eqGate_zero (a b : Limbs n) : E.EqGate a b 0 := E.fixedGate_zero _ _
@[simp] theorem negGate_zero (a b : Limbs n) : E.NegGate a b 0 := E.fixedGate_zero _ _
@[simp] theorem invGate_zero (a b inv : Limbs n) : E.InvGate a b inv 0 := E.fixedGate_zero _ _

theorem eqGate_one_iff {a b : Limbs n} (ha : WellFormed E.params.B a)
    (hb : WellFormed E.params.B b) : E.EqGate a b 1 ↔ E.limbValue a = E.limbValue b := by
  rw [EqGate, E.fixedGate_one_iff _ _ (by intro i; fin_cases i <;>
    first | exact ha | exact hb | exact E.zero_limbs_bounded)]
  simp [GateKind.expression, Expression.value, sub_eq_zero]

theorem negGate_one_iff {a b : Limbs n} (ha : WellFormed E.params.B a)
    (hb : WellFormed E.params.B b) : E.NegGate a b 1 ↔ E.limbValue a = -E.limbValue b := by
  rw [NegGate, E.fixedGate_one_iff _ _ (by intro i; fin_cases i <;>
    first | exact ha | exact hb | exact E.zero_limbs_bounded)]
  simp [GateKind.expression, Expression.value, eq_neg_iff_add_eq_zero]

theorem invGate_one_iff {a b inv : Limbs n} (ha : WellFormed E.params.B a)
    (hb : WellFormed E.params.B b) (hi : WellFormed E.params.B inv) :
    E.InvGate a b inv 1 ↔ (E.limbValue a-E.limbValue b)*E.limbValue inv = 1 := by
  rw [InvGate, E.fixedGate_one_iff _ _ (by intro i; fin_cases i <;>
    first | exact ha | exact hb | exact hi | exact E.zero_limbs_bounded)]
  simp [GateKind.expression, Expression.value, sub_eq_zero]

/-- An is-zero selector: the prover cannot choose either branch for a nonmatching value. -/
structure ZeroTest (a b inv : Limbs n) (z : ℤ) : Prop where
  bit : E.NativeBit z
  zero : E.EqGate a b z
  nonzero : E.InvGate a b inv (1-z)

theorem zeroTest_iff {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    {a b inv : Limbs n} (ha : WellFormed E.params.B a) (hb : WellFormed E.params.B b)
    (hi : WellFormed E.params.B inv) (z : ℤ) :
    E.ZeroTest a b inv z ↔
      (z = 1 ∧ E.limbValue a = E.limbValue b) ∨
      (z = 0 ∧ (E.limbValue a-E.limbValue b)*E.limbValue inv = 1) := by
  constructor
  · intro h
    rcases E.nativeBit_cases hp h.bit with hz | hz
    · right
      exact ⟨hz, (E.invGate_one_iff ha hb hi).mp (by simpa [hz] using h.nonzero)⟩
    · exact Or.inl ⟨hz, (E.eqGate_one_iff ha hb).mp (by simpa [hz] using h.zero)⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨E.nativeBit_one, (E.eqGate_one_iff ha hb).mpr h, by simp⟩
    · exact ⟨E.nativeBit_zero, by simp, by simpa using (E.invGate_one_iff ha hb hi).mpr h⟩

theorem zeroTest_selector {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    {a b inv : Limbs n} (ha : WellFormed E.params.B a) (hb : WellFormed E.params.B b)
    (hi : WellFormed E.params.B inv) {z : ℤ} (h : E.ZeroTest a b inv z) :
    z = 1 ↔ E.limbValue a = E.limbValue b := by
  rcases (E.zeroTest_iff hp ha hb hi z).mp h with ⟨hz, he⟩ | ⟨hz, he⟩
  · simp [hz, he]
  · have hn : E.limbValue a ≠ E.limbValue b := by intro heq; simp [heq] at he
    simp [hz, hn]

/-- All gate occurrences below read this same ten-vector assignment:
px, py, qx, qy, rx, ry, slope, inverse-x, inverse-y, negative-qy. -/
abbrev CompleteWires (n : ℕ) := Fin 10 → Limbs n

def WiresBounded (x : CompleteWires n) := ∀ i, WellFormed E.params.B (x i)
def wireP (x : CompleteWires n) : Coordinates (ZMod q) := ⟨E.limbValue (x 0), E.limbValue (x 1)⟩
def wireQ (x : CompleteWires n) : Coordinates (ZMod q) := ⟨E.limbValue (x 2), E.limbValue (x 3)⟩
def wireR (x : CompleteWires n) : Coordinates (ZMod q) := ⟨E.limbValue (x 4), E.limbValue (x 5)⟩

def AddGates (x : CompleteWires n) (s : ℤ) :=
  E.FixedGate .slopePlus ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,0] s ∧
  E.FixedGate .xout ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,0] s ∧
  E.FixedGate .slopeMinus ![x 0,x 1,x 4,x 5,0,0,x 6,0] s

def DoubleGates (x : CompleteWires n) (s : ℤ) :=
  E.FixedGate .tangent ![x 0,x 1,x 0,x 1,x 4,x 5,x 6,0] s ∧
  E.FixedGate .xout ![x 0,x 1,x 0,x 1,x 4,x 5,x 6,0] s ∧
  E.FixedGate .slopeMinus ![x 0,x 1,x 4,x 5,0,0,x 6,0] s

@[simp] theorem addGates_zero (x : CompleteWires n) : E.AddGates x 0 :=
  ⟨E.fixedGate_zero _ _, E.fixedGate_zero _ _, E.fixedGate_zero _ _⟩
@[simp] theorem doubleGates_zero (x : CompleteWires n) : E.DoubleGates x 0 :=
  ⟨E.fixedGate_zero _ _, E.fixedGate_zero _ _, E.fixedGate_zero _ _⟩

theorem addGates_one_iff {x : CompleteWires n} (hx : E.WiresBounded x) :
    E.AddGates x 1 ↔ AddChecks (E.wireP x) (E.wireQ x) (E.wireR x) (E.limbValue (x 6)) := by
  have hb (i0 i1 i2 i3 i4 i5 i6 : Fin 10) :
      ∀ a, WellFormed E.params.B (![x i0,x i1,x i2,x i3,x i4,x i5,x i6,0] a) := by
    intro a; fin_cases a <;> first | exact hx _ | exact E.zero_limbs_bounded
  have ho : ∀ a, WellFormed E.params.B (![x 0,x 1,x 4,x 5,0,0,x 6,0] a) := by
    intro a; fin_cases a <;> first | exact hx _ | exact E.zero_limbs_bounded
  rw [AddGates, E.fixedGate_one_iff _ _ (hb 0 1 2 3 4 5 6),
    E.fixedGate_one_iff _ _ (hb 0 1 2 3 4 5 6), E.fixedGate_one_iff _ _ ho]
  simp [GateKind.expression, Expression.value]
  constructor
  · intro h
    exact ⟨by simpa [wireP, wireQ, mul_comm] using h.1,
      by simpa [wireP, wireQ, wireR, pow_two] using h.2.1,
      by simpa [wireP, wireR, mul_comm] using h.2.2⟩
  · intro h
    exact ⟨by simpa [wireP, wireQ, mul_comm] using h.slope_eq,
      by simpa [wireP, wireQ, wireR, pow_two] using h.x_eq,
      by simpa [wireP, wireR, mul_comm] using h.y_eq⟩

theorem doubleGates_one_iff {x : CompleteWires n} (hx : E.WiresBounded x) :
    E.DoubleGates x 1 ↔ DoubleChecks C (E.wireP x) (E.wireR x) (E.limbValue (x 6)) := by
  have hb : ∀ a, WellFormed E.params.B (![x 0,x 1,x 0,x 1,x 4,x 5,x 6,0] a) := by
    intro a; fin_cases a <;> first | exact hx _ | exact E.zero_limbs_bounded
  have ho : ∀ a, WellFormed E.params.B (![x 0,x 1,x 4,x 5,0,0,x 6,0] a) := by
    intro a; fin_cases a <;> first | exact hx _ | exact E.zero_limbs_bounded
  rw [DoubleGates, E.fixedGate_one_iff _ _ hb, E.fixedGate_one_iff _ _ hb,
    E.fixedGate_one_iff _ _ ho]
  simp [GateKind.expression, Expression.value]
  constructor
  · intro h
    exact ⟨by simpa [wireP, pow_two] using h.1,
      by simpa [wireP, wireR, pow_two, two_mul] using h.2.1,
      by simpa [wireP, wireR, mul_comm] using h.2.2⟩
  · intro h
    exact ⟨by simpa [wireP, pow_two] using h.slope_eq,
      by simpa [wireP, wireR, pow_two, two_mul] using h.x_eq,
      by simpa [wireP, wireR, mul_comm] using h.y_eq⟩

end EfficientFFA.Native.ECEncoding
