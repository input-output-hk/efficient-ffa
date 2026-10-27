import EfficientFFA.Representation

namespace EfficientFFA.ShiftedEncoding

/-- The paper's shifted integer interpretation, before reduction modulo q. -/
def value {n : ℕ} (B : ℤ) (x : Limbs n) : ℤ := 1 + eval B x

/-- With capacity below 2q, a zero residue has the unique integer value q. -/
theorem zero_iff_eval {n : ℕ} {B q : ℤ} (hB : 0 < B)
    (hcap : B ^ n < 2*q) {x : Limbs n} (hx : WellFormed B x) :
    value B x ≡ 0 [ZMOD q] ↔ eval B x = q-1 := by
  constructor
  · intro hz
    have hb := eval_bounds hB hx
    have hq : q ≡ 0 [ZMOD q] := by simp [Int.ModEq]
    have hm : value B x - q ≡ 0 [ZMOD q] := by
      simpa using (hz.trans hq.symm).sub (Int.ModEq.refl q)
    have he := eq_zero_of_modEq_of_bounds hm
      (show -q < value B x - q by dsimp [value]; omega)
      (show value B x - q < q by dsimp [value]; omega)
    dsimp [value] at he
    omega
  · intro he
    simp [value, he, Int.ModEq]

/-- Exactly one bounded limb vector encodes zero under the paper's capacity condition. -/
theorem exists_unique_zero {n : ℕ} {B q : ℤ} (hB : 0 < B) (hq : 0 < q)
    (hlo : q ≤ B ^ n) (hhi : B ^ n < 2*q) :
    ∃! x : Limbs n, WellFormed B x ∧ value B x ≡ 0 [ZMOD q] := by
  obtain ⟨z, hz, he⟩ := exists_limbs hB n (by omega : 0 ≤ q-1) (by omega : q-1 < B^n)
  refine ⟨z, ⟨hz, (zero_iff_eval hB hhi hz).mpr he⟩, ?_⟩
  intro x hx
  apply eval_injective hB hx.1 hz
  exact ((zero_iff_eval hB hhi hx.1).mp hx.2).trans he.symm

/-- A limb-wise comparison against a known zero representation is a sound and
complete zero test. Other foreign residues need not have unique representations. -/
theorem zero_iff_limbs {n : ℕ} {B q : ℤ} (hB : 0 < B) (hcap : B ^ n < 2*q)
    {x zero : Limbs n} (hx : WellFormed B x) (hz : WellFormed B zero)
    (hzero : value B zero ≡ 0 [ZMOD q]) :
    value B x ≡ 0 [ZMOD q] ↔ ∀ i, x i = zero i := by
  constructor
  · intro h
    have he : eval B x = eval B zero :=
      ((zero_iff_eval hB hcap hx).mp h).trans ((zero_iff_eval hB hcap hz).mp hzero).symm
    exact congrFun (eval_injective hB hx hz he)
  · intro h
    simpa only [funext h] using hzero

/-- Every foreign value also has a shifted representation when capacity suffices. -/
theorem exists_representation {n : ℕ} {B q : ℤ} (hB : 0 < B) (hq : 0 < q)
    (hcap : q ≤ B^n) (a : ℤ) :
    ∃ x : Limbs n, WellFormed B x ∧ value B x ≡ a [ZMOD q] := by
  obtain ⟨x, hx, he⟩ := exists_canonical_limbs hB hq n hcap (a-1)
  refine ⟨x, hx, ?_⟩
  dsimp [value]
  rw [he]
  have hm : (a-1) % q ≡ a-1 [ZMOD q] := by simp [Int.ModEq]
  simpa using (Int.ModEq.refl 1).add hm

/-- Native limb equality implements the zero test when bounded limbs fit in
one native residue interval. The radix condition is a parameter condition. -/
theorem zero_iff_native_checks {n : ℕ} {B q p : ℤ} (hB : 0 < B)
    (hcap : B ^ n < 2*q) (hnative : B ≤ p) {x zero : Limbs n}
    (hx : WellFormed B x) (hz : WellFormed B zero)
    (hzero : value B zero ≡ 0 [ZMOD q]) :
    value B x ≡ 0 [ZMOD q] ↔ ∀ i, x i ≡ zero i [ZMOD p] := by
  rw [zero_iff_limbs hB hcap hx hz hzero]
  constructor
  · intro he i
    rw [he i]
  · intro hm i
    have hd : x i - zero i ≡ 0 [ZMOD p] := by
      simpa using (hm i).sub (Int.ModEq.refl (zero i))
    have hxi := hx i
    have hzi := hz i
    have he := eq_zero_of_modEq_of_bounds hd (by omega) (by omega)
    omega

end EfficientFFA.ShiftedEncoding
