import EfficientFFA.Native.Expression
import Mathlib.Data.ZMod.Basic

namespace EfficientFFA.Native

/-- Native bitness is sufficient only with a field modulus and a canonical lift. -/
theorem bit_cases {p : ℕ} [Fact p.Prime] {s : ℤ}
    (hs : 0 ≤ s ∧ s < p) (hb : s*(s-1) ≡ 0 [ZMOD (p : ℤ)]) : s = 0 ∨ s = 1 := by
  have he : (s : ZMod p)*((s : ZMod p)-1) = 0 := by
    rw [← ZMod.intCast_eq_intCast_iff] at hb
    simpa using hb
  rcases mul_eq_zero.mp he with hz | ho
  · left
    have h : s ≡ 0 [ZMOD (p : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]; simpa using hz
    simpa [Int.ModEq, Int.emod_eq_of_lt hs.1 hs.2] using h
  · right
    have hp : (1 : ℤ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have h : s ≡ 1 [ZMOD (p : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]; simpa using sub_eq_zero.mp ho
    simpa [Int.ModEq, Int.emod_eq_of_lt hs.1 hs.2, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 1) hp] using h

namespace Parameters
variable {r : ℕ} {α : Type*} (P : Parameters r)

structure Activated (e : Polynomial α) (x : α → ℤ) (s u : ℤ) (v : Fin r → ℤ) : Prop where
  bit_range : 0 ≤ s ∧ s < P.p
  bit_check : s*(s-1) ≡ 0 [ZMOD P.p]
  u_range : 0 ≤ u ∧ u < P.Umax
  v_range : ∀ a, 0 ≤ v a ∧ v a < P.Vmax a
  native : s*P.nativeResidual e x u ≡ 0 [ZMOD P.p]
  auxiliary : ∀ a, s*P.auxResidual e x u (v a) a ≡ 0 [ZMOD P.p]

theorem activated_sound {p : ℕ} [Fact p.Prime] (hp : P.p = p)
    {e : Polynomial α} (hv : P.Valid e) {x : α → ℤ} {s u : ℤ} {v : Fin r → ℤ}
    (hx : Polynomial.Bounded P.B x) (ha : P.Activated e x s u v) :
    s = 0 ∨ (s = 1 ∧ Polynomial.eval e x ≡ 0 [ZMOD P.q]) := by
  have hb := bit_cases (p := p) (by simpa [← hp] using ha.bit_range)
    (by simpa [← hp] using ha.bit_check)
  rcases hb with hz | ho
  · exact Or.inl hz
  · refine Or.inr ⟨ho, P.sound hv.positive hv.nowrap (u := u) (v := v) hx ?_⟩
    exact ⟨ha.u_range, ha.v_range, by simpa [ho] using ha.native,
      fun a => by simpa [ho] using ha.auxiliary a⟩

theorem activated_one {e : Polynomial α} {x : α → ℤ} {u : ℤ} {v : Fin r → ℤ}
    (hp : 1 < P.p) (ha : P.Accepts e x u v) : P.Activated e x 1 u v := by
  exact ⟨⟨by omega, hp⟩, by simp, ha.u_range, ha.v_range,
    by simpa using ha.native, fun a => by simpa using ha.auxiliary a⟩

theorem activated_zero (hp : 0 < P.p) (e : Polynomial α) (x : α → ℤ) :
    P.Activated e x 0 0 (fun _ => 0) := by
  refine ⟨⟨by omega, hp⟩, by simp, ⟨by omega, ?_⟩, ?_, by simp, fun _ => by simp⟩
  · exact pow_pos (by omega) _
  · intro a
    exact ⟨by omega, pow_pos (by omega) _⟩

end Parameters
end EfficientFFA.Native
