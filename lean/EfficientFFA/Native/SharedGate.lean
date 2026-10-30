import EfficientFFA.Native.Trace

namespace EfficientFFA.Native.ECEncoding
open EllipticCurve
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

/-- A gate with fixed input limbs. Only quotient witnesses are local to the gate. -/
def FixedGate (k : GateKind) (x : Fin 8 → Limbs n) (s : ℤ) : Prop :=
  ∃ u v, E.params.Activated ((k.expression C.a.val C.b.val).compile E.params.B n)
    (fun a => x a.1 a.2) s u v

def limbValue (x : Limbs n) : ZMod q := eval E.params.B x

theorem fixedGate_zero (k : GateKind) (x : Fin 8 → Limbs n) : E.FixedGate k x 0 :=
  ⟨0, fun _ => 0, E.params.activated_zero (E.valid k).positive.native _ _⟩

theorem fixedGate_one_iff (k : GateKind) (x : Fin 8 → Limbs n)
    (hx : ∀ a, WellFormed E.params.B (x a)) :
    E.FixedGate k x 1 ↔ (k.expression C.a.val C.b.val).value (fun a => E.limbValue (x a)) = 0 := by
  constructor
  · rintro ⟨u, v, ha⟩
    apply (E.check_iff k _).mp
    exact ⟨fun a => x a.1 a.2, fun a => hx a.1 a.2, fun _ => rfl, u, v, ha⟩
  · intro he
    have hd : Polynomial.eval ((k.expression C.a.val C.b.val).compile E.params.B n)
        (fun a => x a.1 a.2) ≡ 0 [ZMOD E.params.q] := by
      rw [E.foreign_eq, ← ZMod.intCast_eq_intCast_iff, Int.cast_zero,
        Expression.compile_eval, Expression.cast_value]
      exact he
    exact ⟨_, _, E.params.activated_one E.native_gt_one
      (E.params.witnesses_accept (E.valid k).positive (E.valid k).widths (fun a => hx a.1 a.2) hd)⟩

/-- Native bit constraints, on a canonical integer representative of the field wire. -/
def NativeBit (b : ℤ) : Prop := 0 ≤ b ∧ b < E.params.p ∧ b*(b-1) ≡ 0 [ZMOD E.params.p]

theorem nativeBit_cases {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    {b : ℤ} (hb : E.NativeBit b) : b = 0 ∨ b = 1 :=
  Native.bit_cases (p := p) (by simpa [← hp] using And.intro hb.1 hb.2.1)
    (by simpa [← hp] using hb.2.2)

theorem nativeBit_zero : E.NativeBit 0 := by
  have hp := E.native_gt_one
  simp only [NativeBit]
  exact ⟨by omega, by omega, by simp⟩

theorem nativeBit_one : E.NativeBit 1 := by
  exact ⟨by omega, E.native_gt_one, by simp⟩

/-- Copy constraints use native equality of the actual limbs, not equality modulo q. -/
def CopyLimbs (s : ℤ) (x y : Limbs n) : Prop :=
  ∀ i, s * (x i - y i) ≡ 0 [ZMOD E.params.p]

@[simp] theorem copyLimbs_zero (x y : Limbs n) : E.CopyLimbs 0 x y := by
  intro i
  simp

theorem copyLimbs_one_iff (hfit : E.params.B ≤ E.params.p) {x y : Limbs n}
    (hx : WellFormed E.params.B x) (hy : WellFormed E.params.B y) :
    E.CopyLimbs 1 x y ↔ x = y := by
  constructor
  · intro hc
    funext i
    have hi : x i ≡ y i [ZMOD E.params.p] := by
      have h := hc i
      simpa only [one_mul, Int.modEq_iff_dvd, zero_sub, neg_sub] using h
    have hxi := hx i
    have hyi := hy i
    simpa only [Int.ModEq, Int.emod_eq_of_lt hxi.1 (lt_of_lt_of_le hxi.2 hfit),
      Int.emod_eq_of_lt hyi.1 (lt_of_lt_of_le hyi.2 hfit)] using hi
  · rintro rfl
    intro i
    simp

/-- One deterministic encoding per foreign value, reusable at every occurrence. -/
theorem exists_limbValue (v : ZMod q) : ∃ x : Limbs n,
    WellFormed E.params.B x ∧ E.limbValue x = v := by
  obtain ⟨x, hx, he⟩ := exists_canonical_limbs (E.valid .equal).positive.radix
    (E.valid .equal).positive.foreign n E.capacity v.val
  refine ⟨x, hx, ?_⟩
  dsimp [limbValue]
  rw [he, E.foreign_eq, ZMod.intCast_mod]
  simp

noncomputable def canonicalLimbs (v : ZMod q) : Limbs n :=
  Classical.choose (E.exists_limbValue v)

theorem canonicalLimbs_bounded (v : ZMod q) : WellFormed E.params.B (E.canonicalLimbs v) :=
  (Classical.choose_spec (E.exists_limbValue v)).1

@[simp] theorem limbValue_canonical (v : ZMod q) : E.limbValue (E.canonicalLimbs v) = v :=
  (Classical.choose_spec (E.exists_limbValue v)).2

end EfficientFFA.Native.ECEncoding
