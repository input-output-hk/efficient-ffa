import Mathlib

/-!
# Integer reconstruction from a finite family of congruences

Developed from the LCM argument of the paper (sec:overview, sec:ffa-mul).
The moduli need not be coprime. Zero and negative moduli are permitted in
this arithmetic layer; concrete constraint parameters will require positivity.
-/

namespace EfficientFFA

/-- LCM of a finite list of integer moduli; the empty family's LCM is one. -/
def moduliLCM : List ℤ → ℤ
  | [] => 1
  | m :: ms => Int.lcm m (moduliLCM ms)

/-- Simultaneous congruences are equivalent to congruence modulo the LCM. -/
theorem congruent_all_iff_lcm (ms : List ℤ) (a b : ℤ) :
    (∀ m ∈ ms, a ≡ b [ZMOD m]) ↔ a ≡ b [ZMOD moduliLCM ms] := by
  induction ms with
  | nil => simp [moduliLCM, Int.ModEq]
  | cons m ms ih =>
    rw [List.forall_mem_cons, ih, moduliLCM]
    exact Int.modEq_and_modEq_iff_modEq_lcm

/-- A congruence cannot wrap around when its residual is strictly inside
(-m,m). The strict endpoints are essential. -/
theorem eq_zero_of_modEq_of_bounds {m x : ℤ}
    (hmod : x ≡ 0 [ZMOD m]) (hlo : -m < x) (hhi : x < m) : x = 0 := by
  have hm : 0 < m := by omega
  have hd : m ∣ x := Int.modEq_zero_iff_dvd.mp hmod
  rcases hd with ⟨k, rfl⟩
  by_cases hk : k = 0
  · simp [hk]
  · rcases lt_or_gt_of_ne hk with hk | hk
    · have : k ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ k := by omega
      nlinarith

/-- The paper's reconstruction step, without a coprimality assumption. -/
theorem eq_zero_of_congruences_of_bounds {ms : List ℤ} {x : ℤ}
    (hmod : ∀ m ∈ ms, x ≡ 0 [ZMOD m])
    (hlo : -moduliLCM ms < x) (hhi : x < moduliLCM ms) : x = 0 := by
  exact eq_zero_of_modEq_of_bounds ((congruent_all_iff_lcm ms x 0).mp hmod) hlo hhi

end EfficientFFA
