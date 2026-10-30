import EfficientFFA.Native.Subgroup
import EfficientFFA.Instances.Curve17

namespace EfficientFFA.Instances.Subgroup17
open EllipticCurve Native MSM
open scoped ENNReal

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- A curve with 22 points, cofactor two, and a subgroup of order eleven. -/
def curve : Curve (ZMod 17) where
  a := 2
  b := 3
  smooth := by decide
instance : Fintype curve.Point := curve.pointFintype

theorem cardinality : Nat.card curve.Point = 22 := by
  rw [curve.natCard_points]
  have h : Nat.card {xy : ZMod 17 × ZMod 17 // xy.2^2 = xy.1^3+2*xy.1+3} = 21 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact congrArg (fun k => k+1) h

def prebase : Coordinates (ZMod 17) := ⟨2,7⟩
def base : Coordinates (ZMod 17) := ⟨14,15⟩
def torsion : Coordinates (ZMod 17) := ⟨16,0⟩
theorem prebase_on : curve.OnCurve prebase := by unfold Curve.OnCurve; decide
theorem base_on : curve.OnCurve base := by unfold Curve.OnCurve; decide
theorem torsion_on : curve.OnCurve torsion := by unfold Curve.OnCurve; decide

theorem base_double : curve.point base base_on = (2 : ℕ) • curve.point prebase prebase_on := by
  obtain ⟨_, he⟩ := curve.doubling_sound prebase_on
    (show DoubleChecks curve prebase base 1 from by constructor <;> decide)
  simpa only [two_smul] using he

theorem base_order : addOrderOf (curve.point base base_on) = 11 := by
  apply addOrderOf_eq_prime _ (curve.point_ne_zero base_on)
  rw [base_double, ← mul_nsmul]
  have h : Nat.card curve.Point • curve.point prebase prebase_on = 0 := card_nsmul_eq_zero'
  simpa only [cardinality] using h

def subgroup : AddSubgroup curve.Point := AddSubgroup.zmultiples (curve.point base base_on)
noncomputable instance : Fintype subgroup := Fintype.ofFinite subgroup

theorem subgroup_cardinality : Nat.card subgroup = 11 := by
  rw [subgroup, Nat.card_zmultiples, base_order]
theorem subgroup_fintype_cardinality : Fintype.card subgroup = 11 := by
  simpa only [Nat.card_eq_fintype_card] using subgroup_cardinality

theorem base_mem : curve.point base base_on ∈ subgroup := AddSubgroup.mem_zmultiples _

theorem quotient_cardinality : Nat.card (curve.Point ⧸ subgroup) = 2 := by
  have h := subgroup.card_eq_card_quotient_mul_card_addSubgroup
  rw [cardinality, subgroup_cardinality] at h
  omega

theorem coprime_cofactor : (Nat.card (curve.Point ⧸ subgroup)).Coprime (Nat.card subgroup) := by
  rw [quotient_cardinality, subgroup_cardinality]
  decide

theorem torsion_double : curve.point torsion torsion_on + curve.point torsion torsion_on = 0 :=
  (curve.double_eq_zero_iff torsion_on).mpr (by decide)

/-- This curve cannot satisfy the old ambient radix-injectivity premise. -/
theorem ambient_double_not_injective : ¬ Function.Injective (fun p : curve.Point => (2 : ℕ) • p) := by
  intro h
  apply curve.point_ne_zero torsion_on
  apply h
  simpa [two_smul] using torsion_double

theorem torsion_not_mem : curve.point torsion torsion_on ∉ subgroup := by
  intro hm
  have hz := (Subgroup.mem_iff_card_nsmul_eq_zero subgroup coprime_cofactor _).mp hm
  rw [subgroup_cardinality] at hz
  have htwo : (2 : ℕ) • curve.point torsion torsion_on = 0 := by simpa [two_smul] using torsion_double
  have he : (11 : ℕ) • curve.point torsion torsion_on = curve.point torsion torsion_on := by
    calc
      _ = (5*2+1 : ℕ) • curve.point torsion torsion_on := rfl
      _ = curve.point torsion torsion_on := by rw [add_smul, mul_smul, htwo]; simp
  exact curve.point_ne_zero torsion_on (he.symm.trans hz)

/-- Reuse the earlier small radix/moduli; check every gate for the new curve coefficient. -/
theorem valid (k : GateKind) : Curve17.params.Valid ((k.expression 2 3).compile 5 2) := by
  cases k <;> constructor <;> constructor <;> decide

def encoding : ECEncoding curve 2 1 where
  params := Curve17.params
  foreign_eq := rfl
  capacity := by decide
  valid k := valid k
  native_gt_one := by decide

theorem base_member_checks : encoding.Member subgroup base :=
  (encoding.member_iff subgroup coprime_cofactor base).mpr ⟨base_on, base_mem⟩

theorem reject_torsion : ¬ encoding.Member subgroup torsion := by
  intro h
  obtain ⟨_, hm⟩ := (encoding.member_iff subgroup coprime_cofactor torsion).mp h
  exact torsion_not_mem hm

theorem failure_bound (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < 2 → ∀ j, j < 1 → windows i j < 2) :
    (PMF.uniformOfFintype subgroup).toOuterMeasure
      {u | ¬ encoding.TraceWitnesses 1 1 2 (fun _ => base) (descending windows 2) (u : curve.Point)} ≤
        (8 : ℝ≥0∞)/11 := by
  have hp : Nat.Prime (Nat.card subgroup) := by rw [subgroup_cardinality]; decide
  have hs : (2^1 : ℕ)*(1 : ℤ)+(2^1 : ℕ)-1 < (Nat.card subgroup : ℤ) := by
    rw [subgroup_cardinality]; norm_num
  have h := encoding.uniform_subgroup_failure_bound_checked subgroup 1 1 2 (by decide) (by decide)
    (fun _ => base) (fun _ => base_member_checks) coprime_cofactor windows hrange hp hs
  simpa [failureBudget, subgroup_fintype_cardinality] using h

theorem exists_correct (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < 2 → ∀ j, j < 1 → windows i j < 2) :
    ∃ u : subgroup, ∃ tr : CoordinateTrace (ZMod 17),
      encoding.Trace 1 1 2 (fun _ => base) (descending windows 2) tr ∧
      (∃ hs : curve.OnCurve tr.seed, curve.point tr.seed hs = (u : curve.Point)) ∧
      ∃ hout : curve.Valid tr.output, curve.decode tr.output hout =
        ∑ j ∈ Finset.range 1, (∑ i ∈ Finset.range 2, (2^1)^i*windows i j) •
          curve.point base base_on ∧ curve.decode tr.output hout ∈ subgroup := by
  apply encoding.exists_correct_subgroup_trace subgroup 1 1 2 (by decide) (by decide)
    (fun _ => base) (fun _ => base_on) (fun _ => base_mem) windows hrange
  · rw [subgroup_cardinality]; decide
  · rw [subgroup_cardinality]; norm_num
  · rw [subgroup_fintype_cardinality]; decide

end EfficientFFA.Instances.Subgroup17
