import EfficientFFA

namespace EfficientFFA.Tests.Subgroup
open EllipticCurve Native MSM

-- The ambient group is composite and has two-torsion; the subgroup has prime order.
example : ¬ Nat.Prime (Nat.card Instances.Subgroup17.curve.Point) := by
  rw [Instances.Subgroup17.cardinality]
  decide
example : Nat.Prime (Nat.card Instances.Subgroup17.subgroup) := by
  rw [Instances.Subgroup17.subgroup_cardinality]
  decide
example : ¬ Function.Injective (fun p : Instances.Subgroup17.curve.Point => (2 : ℕ) • p) :=
  Instances.Subgroup17.ambient_double_not_injective
example : Function.Injective (fun p : Instances.Subgroup17.subgroup => (2 : ℕ) • p) := by
  apply prime_radix_injective 2 1 (by decide) (by decide)
  · rw [Instances.Subgroup17.subgroup_cardinality]; decide
  · rw [Instances.Subgroup17.subgroup_cardinality]; norm_num

-- Scalar annihilation alone cannot select a particular prime-order subgroup.
-- Here both the chosen subgroup and the quotient have order five.
private def axis : AddSubgroup (ZMod 5 × ZMod 5) where
  carrier := {x | x.2 = 0}
  zero_mem' := rfl
  add_mem' := by intro a b ha hb; change a.2+b.2 = 0; rw [ha,hb,zero_add]
  neg_mem' := by intro a ha; change -a.2 = 0; rw [ha,neg_zero]

private def axisEquiv : axis ≃ ZMod 5 where
  toFun x := x.val.1
  invFun x := ⟨(x,0),rfl⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,h⟩
    change y = 0 at h
    subst y
    rfl
  right_inv _ := rfl

private theorem axis_card : Nat.card axis = 5 := by
  rw [Nat.card_congr axisEquiv]
  exact Nat.card_zmod 5

private theorem axis_quotient_card : Nat.card ((ZMod 5 × ZMod 5) ⧸ axis) = 5 := by
  have h := axis.card_eq_card_quotient_mul_card_addSubgroup
  have hg : Nat.card (ZMod 5 × ZMod 5) = 25 := by
    rw [Nat.card_prod, Nat.card_zmod]
  rw [hg, axis_card] at h
  omega

example : ¬ (Nat.card ((ZMod 5 × ZMod 5) ⧸ axis)).Coprime (Nat.card axis) := by
  rw [axis_quotient_card, axis_card]
  decide

example : ¬ ((0,1) : ZMod 5 × ZMod 5) ∈ axis ∧
    Nat.card axis • ((0,1) : ZMod 5 × ZMod 5) = 0 := by
  rw [axis_card]
  constructor
  · change (1 : ZMod 5) ≠ 0
    decide
  · decide

-- Native point loading accepts the generator and rejects the ambient two-torsion point.
example : Instances.Subgroup17.encoding.Member Instances.Subgroup17.subgroup Instances.Subgroup17.base :=
  Instances.Subgroup17.base_member_checks
example : ¬ Instances.Subgroup17.encoding.Member Instances.Subgroup17.subgroup Instances.Subgroup17.torsion :=
  Instances.Subgroup17.reject_torsion

end EfficientFFA.Tests.Subgroup

#print axioms EfficientFFA.MSM.map_entry
#print axioms EfficientFFA.MSM.map_addRows
#print axioms EfficientFFA.MSM.map_loop
#print axioms EfficientFFA.MSM.tableSafe_map_iff
#print axioms EfficientFFA.MSM.collision_map_iff
#print axioms EfficientFFA.MSM.groupAccepts_map_iff
#print axioms EfficientFFA.EllipticCurve.Curve.trace_complete_subgroup
#print axioms EfficientFFA.EllipticCurve.Curve.trace_output_mem_subgroup
#print axioms EfficientFFA.EllipticCurve.Curve.uniform_subgroup_trace_failure_bound_prime
#print axioms EfficientFFA.EllipticCurve.Curve.exists_correct_subgroup_trace
#print axioms EfficientFFA.Native.ECEncoding.trace_output_mem_subgroup
#print axioms EfficientFFA.Native.ECEncoding.member_iff
#print axioms EfficientFFA.Native.ECEncoding.uniform_subgroup_failure_bound
#print axioms EfficientFFA.Native.ECEncoding.exists_correct_subgroup_trace
#print axioms EfficientFFA.Native.ECEncoding.uniform_subgroup_failure_bound_checked
#print axioms EfficientFFA.Instances.Subgroup17.cardinality
#print axioms EfficientFFA.Instances.Subgroup17.prebase_on
#print axioms EfficientFFA.Instances.Subgroup17.base_on
#print axioms EfficientFFA.Instances.Subgroup17.torsion_on
#print axioms EfficientFFA.Instances.Subgroup17.base_double
#print axioms EfficientFFA.Instances.Subgroup17.base_order
#print axioms EfficientFFA.Instances.Subgroup17.subgroup_cardinality
#print axioms EfficientFFA.Instances.Subgroup17.subgroup_fintype_cardinality
#print axioms EfficientFFA.Instances.Subgroup17.base_mem
#print axioms EfficientFFA.Instances.Subgroup17.quotient_cardinality
#print axioms EfficientFFA.Instances.Subgroup17.coprime_cofactor
#print axioms EfficientFFA.Instances.Subgroup17.torsion_double
#print axioms EfficientFFA.Instances.Subgroup17.ambient_double_not_injective
#print axioms EfficientFFA.Instances.Subgroup17.torsion_not_mem
#print axioms EfficientFFA.Instances.Subgroup17.valid
#print axioms EfficientFFA.Instances.Subgroup17.base_member_checks
#print axioms EfficientFFA.Instances.Subgroup17.reject_torsion
#print axioms EfficientFFA.Instances.Subgroup17.failure_bound
#print axioms EfficientFFA.Instances.Subgroup17.exists_correct
#print axioms EfficientFFA.Subgroup.mem_iff_card_nsmul_eq_zero
#print axioms EfficientFFA.EllipticCurve.Curve.scale_infinity_iff
#print axioms EfficientFFA.EllipticCurve.Curve.coordinates_double_witnesses
#print axioms EfficientFFA.EllipticCurve.Curve.trace_complete_of_finite
