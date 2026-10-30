import EfficientFFA.Native.Statistics
import EfficientFFA.EllipticCurve.Cardinality

namespace EfficientFFA.Instances.Curve17
open EllipticCurve Native MSM
open scoped ENNReal

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def curve : Curve (ZMod 17) where
  a := 2
  b := 2
  smooth := by decide

instance : Fintype curve.Point := curve.pointFintype

/-- Kernel enumeration of the 18 affine solutions; infinity is counted separately. -/
theorem cardinality : Nat.card curve.Point = 19 := by
  rw [curve.natCard_points]
  have h : Nat.card {xy : ZMod 17 × ZMod 17 // xy.2^2 = xy.1^3+2*xy.1+2} = 18 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact congrArg (fun k => k+1) h

theorem fintype_cardinality : Fintype.card curve.Point = 19 := by
  simpa only [Nat.card_eq_fintype_card] using cardinality

theorem prime_cardinality : Nat.Prime (Nat.card curve.Point) := by rw [cardinality]; decide

/-- Two radix-5 limbs represent every residue modulo 17. The auxiliary modulus is
101; the deliberately generous native prime is 65537. No cost claim is made. -/
def params : Parameters 1 where
  B := 5
  q := 17
  p := 65537
  M := fun _ => 101
  t := 7
  tm := fun _ => 7

theorem native_prime : Nat.Prime params.p.toNat := by
  change Nat.Prime 65537
  norm_num

theorem valid (k : GateKind) : params.Valid ((k.expression 2 2).compile 5 2) := by
  cases k <;> constructor <;> constructor <;> decide

def encoding : ECEncoding curve 2 1 where
  params := params
  foreign_eq := rfl
  capacity := by decide
  valid k := valid k
  native_gt_one := by decide

def base : Coordinates (ZMod 17) := ⟨5,1⟩
theorem base_on : curve.OnCurve base := by unfold Curve.OnCurve; decide

theorem parameter_size : (2^1 : ℕ)*(1 : ℤ)+(2^1 : ℕ)-1 < (Nat.card curve.Point : ℤ) := by
  rw [cardinality]; norm_num

theorem budget : failureBudget (2^1) 1 2 < Fintype.card curve.Point := by
  rw [fintype_cardinality]; decide

/-- All parameter and group-cardinality assumptions are discharged for this curve.
The remaining input condition is just that each scalar window is a bit. -/
theorem failure_bound (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < 2 → ∀ j, j < 1 → windows i j < 2) :
    (PMF.uniformOfFintype curve.Point).toOuterMeasure
      {u | ¬ encoding.TraceWitnesses 1 1 2 (fun _ => base) (descending windows 2) u} ≤
        (8 : ℝ≥0∞)/19 := by
  have h := encoding.uniform_littleEndian_failure_bound 1 1 2 (by decide) (by decide)
    (fun _ => base) (fun _ => base_on) windows hrange prime_cardinality parameter_size
  simpa [failureBudget, fintype_cardinality] using h

theorem exists_correct (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < 2 → ∀ j, j < 1 → windows i j < 2) :
    ∃ tr : CoordinateTrace (ZMod 17), encoding.Trace 1 1 2 (fun _ => base) (descending windows 2) tr ∧
      ∃ hout : curve.Valid tr.output, curve.decode tr.output hout =
        ∑ j ∈ Finset.range 1, (∑ i ∈ Finset.range 2, (2^1)^i*windows i j) •
          curve.point base base_on :=
  encoding.exists_correct_trace 1 1 2 (by decide) (by decide) (fun _ => base)
    (fun _ => base_on) windows hrange prime_cardinality parameter_size budget

end EfficientFFA.Instances.Curve17
