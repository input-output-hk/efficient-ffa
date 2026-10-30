import EfficientFFA
import Tests.EllipticCurve

namespace EfficientFFA.Tests.Tables
open EllipticCurve MSM

-- A full accepted table on the earlier concrete curve, built with one repeated base.
private abbrev C7 := EfficientFFA.Tests.EC.C
private abbrev base7 := EfficientFFA.Tests.EC.P
private abbrev start7 := EfficientFFA.Tests.EC.Q
private abbrev mid7 := EfficientFFA.Tests.EC.T

def table7 : ℕ → Coordinates (ZMod 7)
  | 0 => start7
  | 1 => mid7
  | 2 => ⟨1, 4⟩
  | _ => start7

theorem checks7 : TableChecks base7 table7 3 := by
  intro i hi
  interval_cases i
  · exact ⟨2, by constructor <;> decide⟩
  · exact ⟨2, by constructor <;> decide⟩
  · exact ⟨3, by constructor <;> decide⟩

-- Curve validity, all internal x-guards, and group meaning are derived from the checks.
example : ∀ i, i < 3 → (table7 i).x ≠ base7.x :=
  C7.table_guards EfficientFFA.Tests.EC.onP EfficientFFA.Tests.EC.onQ (by decide) checks7

example : ∀ i, i ≤ 3 → ∃ hi : C7.OnCurve (table7 i),
    C7.point (table7 i) hi = i • C7.point base7 EfficientFFA.Tests.EC.onP +
      C7.point start7 EfficientFFA.Tests.EC.onQ ∧ table7 i ≠ base7 :=
  C7.table_sound EfficientFFA.Tests.EC.onP EfficientFFA.Tests.EC.onQ (by decide) checks7

example : TableSafe (C7.point base7 EfficientFFA.Tests.EC.onP)
    (-C7.point start7 EfficientFFA.Tests.EC.onQ) 3 :=
  C7.table_safe EfficientFFA.Tests.EC.onP EfficientFFA.Tests.EC.onQ (by simp [table7]) (by decide) checks7

-- Generic finite-set regressions: the cardinal bound handles small-order bases.
example : (badOffsets (1 : ZMod 7) 3).card = 5 := by decide
example : (badOffsets (2 : ZMod 6) 5).card = 3 := by decide
example : TableSafe (1 : ZMod 7) 4 3 := by
  apply (table_safe_iff_avoids (1 : ZMod 7) 4 (by decide)).mpr
  decide
example : ¬ TableSafe (1 : ZMod 7) 2 3 := by
  rw [table_safe_iff_avoids (1 : ZMod 7) 2 (by decide)]
  decide

instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def C17 : Curve (ZMod 17) where
  a := 2
  b := 2
  smooth := by decide

def base17 : Coordinates (ZMod 17) := ⟨5, 1⟩
def twice17 : Coordinates (ZMod 17) := ⟨6, 3⟩
def three17 : Coordinates (ZMod 17) := ⟨10, 6⟩
def negBase17 : Coordinates (ZMod 17) := ⟨5, 16⟩
def start17 : Coordinates (ZMod 17) := ⟨6, 14⟩

theorem base17_on : C17.OnCurve base17 := by unfold Curve.OnCurve; decide
theorem twice17_on : C17.OnCurve twice17 := by unfold Curve.OnCurve; decide
theorem start17_on : C17.OnCurve start17 := by unfold Curve.OnCurve; decide

-- Known rejected offset V=2P: no accepted table exists. This is covered by
-- offset selection, not by adding per-step table checks.
example : base17.x ≠ twice17.x ∧ start17 = Curve.opposite twice17 := by decide
example : DoubleChecks C17 base17 twice17 13 := by constructor <;> decide
example : AddChecks start17 base17 negBase17 13 := by constructor <;> decide

example : ¬ ∃ table : ℕ → Coordinates (ZMod 17),
    table 0 = start17 ∧ TableChecks base17 table 2 := by
  rintro ⟨table, ht, hc⟩
  obtain ⟨slope, hs⟩ := hc 0 (by decide)
  rw [ht] at hs
  obtain ⟨hsl, hr⟩ := (add_checks_iff (by decide : start17.x ≠ base17.x)).mp hs
  have hchord : chord start17 base17 = 13 :=
    ((add_checks_iff (by decide : start17.x ≠ base17.x)).mp
      (show AddChecks start17 base17 negBase17 13 from by constructor <;> decide)).1.symm
  have hn : table 1 = negBase17 := by
    rw [hr, hsl, hchord]
    decide
  obtain ⟨nextSlope, hnext⟩ := hc 1 (by decide)
  rw [hn] at hnext
  have hh := hnext.slope_eq
  change (1 : ZMod 17) - 16 - nextSlope*(5-5) = 0 at hh
  have hbad : (1 : ZMod 17) - 16 = 0 := by
    simpa only [sub_self, mul_zero, sub_zero] using hh
  exact (by decide : (1 : ZMod 17) - 16 ≠ 0) hbad

-- The repeated-base lemma does not apply to arbitrary changing addends.
-- This isolated example does not satisfy any asserted MSM loop invariant.
def bad17 : Coordinates (ZMod 17) := ⟨14, 11⟩
example : AddChecks base17 twice17 three17 2 ∧
    AddChecks three17 three17 bad17 0 ∧ ¬ C17.OnCurve bad17 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> decide
  · constructor <;> decide
  · unfold Curve.OnCurve
    decide

example : C17.OnCurve three17 := by
  obtain ⟨h, _⟩ := C17.addition_sound base17_on twice17_on
    (by decide) (slope := 2) (R := three17) (by constructor <;> decide)
  exact h

end EfficientFFA.Tests.Tables

-- Trust audit for every new table theorem.
#print axioms EfficientFFA.MSM.entry_succ
#print axioms EfficientFFA.EllipticCurve.x_ne_of_add_checks
#print axioms EfficientFFA.EllipticCurve.Curve.same_x_iff
#print axioms EfficientFFA.EllipticCurve.Curve.repeated_step
#print axioms EfficientFFA.EllipticCurve.Curve.table_sound
#print axioms EfficientFFA.EllipticCurve.Curve.table_guards
#print axioms EfficientFFA.EllipticCurve.Curve.coordinates_on_curve
#print axioms EfficientFFA.EllipticCurve.Curve.point_coordinates
#print axioms EfficientFFA.EllipticCurve.Curve.table_safe
#print axioms EfficientFFA.EllipticCurve.Curve.table_complete
#print axioms EfficientFFA.EllipticCurve.Curve.table_witnesses_iff
#print axioms EfficientFFA.EllipticCurve.Curve.table_lookup_sound
#print axioms EfficientFFA.EllipticCurve.Curve.opposite_on_curve
#print axioms EfficientFFA.EllipticCurve.Curve.point_opposite
#print axioms EfficientFFA.EllipticCurve.Curve.offset_table_witnesses_iff
#print axioms EfficientFFA.MSM.entry_eq_iff
#print axioms EfficientFFA.MSM.table_safe_iff_avoids
#print axioms EfficientFFA.MSM.badOffsets_card_le
#print axioms EfficientFFA.EllipticCurve.Curve.offset_table_iff_avoids
