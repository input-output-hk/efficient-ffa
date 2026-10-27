import EfficientFFA

namespace EfficientFFA.Tests.Native
open EfficientFFA.Native EllipticCurve
private abbrev E := Instances.Curve17.encoding

-- Membership requires both the curve equation and the square linkage.
example : E.OnCurve ⟨5,1⟩ := (E.onCurve_iff _).mpr (by unfold Curve.OnCurve; decide)
example : ¬ E.Check .square ![5,1,0,0,0,0,0,0] := by
  rw [E.check_iff]
  decide
example : ¬ E.OnCurve ⟨5,2⟩ := by
  rw [E.onCurve_iff]
  unfold Curve.OnCurve
  decide

-- Both slope signs and the tangent equation are exercised by real group operations.
example : E.Double ⟨5,1⟩ ⟨6,3⟩ 13 := by
  rw [E.double_iff]
  constructor <;> decide
example : E.Add ⟨5,1⟩ ⟨6,3⟩ ⟨10,6⟩ 2 := by
  rw [E.add_iff]
  constructor <;> decide
example : ¬ E.Add ⟨5,1⟩ ⟨6,3⟩ ⟨10,7⟩ 2 := by
  intro h
  have hy := ((E.add_iff _ _ _ _).mp h).y_eq
  exact (by decide : -(7 : ZMod 17)-1-2*(10-5) ≠ 0) hy
example : ¬ E.Distinct 5 5 := by rw [E.distinct_iff]; simp
example : E.Distinct 5 6 := (E.distinct_iff _ _).mpr (by decide)

-- Ignored infinity coordinates do not collide with active copy branches.
example : E.Complete ⟨⟨5,1⟩,true⟩ ⟨⟨6,3⟩,false⟩ ⟨⟨6,3⟩,false⟩ := by
  apply (E.complete_iff _ _ _).mpr
  exact .left rfl rfl
example : E.Complete ⟨⟨5,1⟩,false⟩ ⟨⟨5,16⟩,false⟩ ⟨⟨0,0⟩,true⟩ := by
  apply (E.complete_iff _ _ _).mpr
  exact .inverse rfl rfl rfl (by decide) rfl
example : ¬ E.Flag false true := by rw [E.flag_iff]; decide

-- The primality condition for raw native bitness is substantive.
example : (3 : ℤ)*(3-1) ≡ 0 [ZMOD 6] ∧ (3 : ℤ) ≠ 0 ∧ (3 : ℤ) ≠ 1 := by decide

-- An inactive identity needs no valid arithmetic relation, even for nonzero residuals.
example : Instances.Curve17.params.Activated (Polynomial.constant 1 : Polynomial (Fin 1))
    (fun _ => 0) 0 0 (fun _ => 0) :=
  Instances.Curve17.params.activated_zero (by decide) _ _

-- Explicit bounded limbs and computed quotient witnesses for the square 5^2 = 8 mod 17.
private def squareWires : Fin 8 × Fin 2 → ℤ := fun a =>
  if a.1 = 0 then (if a.2 = 0 then 0 else 1)
  else if a.1 = 7 then (if a.2 = 0 then 3 else 1) else 0
private def squarePoly := (GateKind.expression 2 2 .square).compile 5 2
example : Instances.Curve17.params.Accepts squarePoly squareWires
    (Instances.Curve17.params.witnessU squarePoly squareWires)
    (Instances.Curve17.params.witnessV squarePoly squareWires) := by
  apply Instances.Curve17.params.witnesses_accept (Instances.Curve17.valid .square).positive
    (Instances.Curve17.valid .square).widths
  · unfold EfficientFFA.Native.Polynomial.Bounded
    decide
  · decide

-- Native congruence alone permits wraparound when reconstruction bounds are omitted.
private def wrapping : Parameters 0 := ⟨20,17,7,Fin.elim0,1,Fin.elim0⟩
example : wrapping.Accepts (Polynomial.wire (0 : Fin 1)) (fun _ => 7) 0 Fin.elim0 := by
  constructor <;> decide
example : ¬ EfficientFFA.Native.Polynomial.eval (Polynomial.wire (0 : Fin 1)) (fun _ => 7) ≡ 0 [ZMOD 17] := by decide

end EfficientFFA.Tests.Native

#print axioms EfficientFFA.Native.Polynomial.eval_constant
#print axioms EfficientFFA.Native.Polynomial.eval_wire
#print axioms EfficientFFA.Native.Polynomial.eval_add
#print axioms EfficientFFA.Native.Polynomial.eval_scale
#print axioms EfficientFFA.Native.Polynomial.eval_mul
#print axioms EfficientFFA.Native.Polynomial.eval_sub
#print axioms EfficientFFA.Native.Polynomial.signedMod_congr
#print axioms EfficientFFA.Native.Polynomial.reduce_congr
#print axioms EfficientFFA.Native.Polynomial.monomial_bounds
#print axioms EfficientFFA.Native.Polynomial.eval_bounds
#print axioms EfficientFFA.Native.Polynomial.eval_congr
#print axioms EfficientFFA.Native.Parameters.residual_congr
#print axioms EfficientFFA.Native.Parameters.residual_bounds
#print axioms EfficientFFA.Native.Parameters.auxCore_bounds
#print axioms EfficientFFA.Native.Parameters.auxCore_congr
#print axioms EfficientFFA.Native.Parameters.sound
#print axioms EfficientFFA.Native.Parameters.witnesses_accept
#print axioms EfficientFFA.Native.Parameters.accepts_iff
#print axioms EfficientFFA.Native.Parameters.accepts_of_rep
#print axioms EfficientFFA.Native.Expression.value_add
#print axioms EfficientFFA.Native.Expression.value_mul
#print axioms EfficientFFA.Native.Expression.value_neg
#print axioms EfficientFFA.Native.Expression.value_sub
#print axioms EfficientFFA.Native.Expression.value_nat
#print axioms EfficientFFA.Native.Expression.limb_eval
#print axioms EfficientFFA.Native.Expression.compile_eval
#print axioms EfficientFFA.Native.Expression.cast_value
#print axioms EfficientFFA.Native.Expression.value_congr
#print axioms EfficientFFA.Native.Expression.checks_sound
#print axioms EfficientFFA.Native.Expression.checks_complete
#print axioms EfficientFFA.Native.Expression.checks_iff
#print axioms EfficientFFA.Native.bit_cases
#print axioms EfficientFFA.Native.Parameters.activated_sound
#print axioms EfficientFFA.Native.Parameters.activated_one
#print axioms EfficientFFA.Native.Parameters.activated_zero
#print axioms EfficientFFA.Native.ECEncoding.check_checks
#print axioms EfficientFFA.Native.ECEncoding.check_iff
#print axioms EfficientFFA.Native.ECEncoding.equal_iff
#print axioms EfficientFFA.Native.ECEncoding.negative_iff
#print axioms EfficientFFA.Native.ECEncoding.distinct_iff
#print axioms EfficientFFA.Native.ECEncoding.copy_iff
#print axioms EfficientFFA.Native.ECEncoding.onCurve_iff
#print axioms EfficientFFA.Native.ECEncoding.add_iff
#print axioms EfficientFFA.Native.ECEncoding.double_iff
#print axioms EfficientFFA.Native.ECEncoding.flag_iff
#print axioms EfficientFFA.Native.ECEncoding.encodedCopy_iff
#print axioms EfficientFFA.Native.ECEncoding.opposite_iff
#print axioms EfficientFFA.Native.ECEncoding.complete_iff
#print axioms EfficientFFA.Native.ECEncoding.scale_iff
#print axioms EfficientFFA.Native.ECEncoding.trace_iff
#print axioms EfficientFFA.Native.ECEncoding.trace_sound_littleEndian
#print axioms EfficientFFA.Native.ECEncoding.traceWitnesses_iff
#print axioms EfficientFFA.Native.ECEncoding.uniform_littleEndian_failure_bound
#print axioms EfficientFFA.Native.ECEncoding.exists_correct_trace
#print axioms EfficientFFA.EllipticCurve.Curve.natCard_points
#print axioms EfficientFFA.Instances.Curve17.cardinality
#print axioms EfficientFFA.Instances.Curve17.fintype_cardinality
#print axioms EfficientFFA.Instances.Curve17.prime_cardinality
#print axioms EfficientFFA.Instances.Curve17.native_prime
#print axioms EfficientFFA.Instances.Curve17.valid
#print axioms EfficientFFA.Instances.Curve17.base_on
#print axioms EfficientFFA.Instances.Curve17.parameter_size
#print axioms EfficientFFA.Instances.Curve17.budget
#print axioms EfficientFFA.Instances.Curve17.failure_bound
#print axioms EfficientFFA.Instances.Curve17.exists_correct
