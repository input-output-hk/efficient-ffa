import EfficientFFA
import Tests.PaperAudit

/-!
# Checked references for PAPER_RESULTS_MAP.md

Each command resolves an existing declaration. Comments identify every mapping
row that uses it. This checks names and elaborated types, not the manual
correspondence judgment or the paper itself. No new mathematical result is
introduced here.
-/

-- F01
#check EfficientFFA.moduliLCM

-- F01
#check EfficientFFA.congruent_all_iff_lcm

-- F02
#check EfficientFFA.eq_zero_of_congruences_of_bounds

-- F02
#check EfficientFFA.eq_zero_of_modEq_of_bounds

-- F03
#check EfficientFFA.eval

-- F03
#check EfficientFFA.WellFormed

-- F03
#check EfficientFFA.exists_limbs

-- F03
#check EfficientFFA.exists_canonical_limbs

-- F03
#check EfficientFFA.eval_bounds

-- F04
#check EfficientFFA.eval_injective

-- F04
#check EfficientFFA.Multiplication.Parameters.canonical_output

-- F05
#check EfficientFFA.LazyArithmetic.lift_unique

-- F05, M06, M08
#check EfficientFFA.Multiplication.Parameters.NoWrap

-- M01
#check EfficientFFA.eval_mul

-- M02
#check EfficientFFA.mulResidual_mod

-- M02
#check EfficientFFA.mulResidual_dvd_iff

-- M02
#check EfficientFFA.multiplication_iff_quotient

-- M03
#check EfficientFFA.Multiplication.weighted_sum_bounds

-- M03
#check EfficientFFA.Multiplication.weighted_product_bounds

-- M03, B02
#check EfficientFFA.Multiplication.Parameters.residual_bounds

-- M04
#check EfficientFFA.Multiplication.quotient_interval

-- M04
#check EfficientFFA.Multiplication.Parameters.kmin

-- M04
#check EfficientFFA.Multiplication.Parameters.kmax

-- M04
#check EfficientFFA.Multiplication.Parameters.lmin

-- M04
#check EfficientFFA.Multiplication.Parameters.lmax

-- M05
#check EfficientFFA.Multiplication.Parameters.nativeResidual

-- M05
#check EfficientFFA.Multiplication.Parameters.Umax

-- M05
#check EfficientFFA.Multiplication.Parameters.WidthBounds

-- M05, M09
#check EfficientFFA.Multiplication.Parameters.Accepts

-- M06
#check EfficientFFA.Multiplication.Parameters.nativeResidual_bounds

-- M06, M10
#check EfficientFFA.Multiplication.Parameters.multiplication_sound

-- M07
#check EfficientFFA.Multiplication.Parameters.auxCore

-- M07
#check EfficientFFA.Multiplication.Parameters.auxResidual

-- M07
#check EfficientFFA.Multiplication.Parameters.auxCore_congr

-- M07, B02
#check EfficientFFA.Multiplication.Parameters.auxCore_bounds

-- M08
#check EfficientFFA.Multiplication.Parameters.auxResidual_bounds

-- M09
#check EfficientFFA.Multiplication.Parameters.accepts_iff_multiplication

-- M11
#check EfficientFFA.Multiplication.Parameters.canonical_witnesses_accept

-- M11
#check EfficientFFA.Multiplication.Parameters.multiplication_complete

-- L01
#check EfficientFFA.eval_add

-- L01
#check EfficientFFA.LazyArithmetic.bounded_add

-- L01
#check EfficientFFA.LazyArithmetic.represents_add

-- L02
#check EfficientFFA.eval_sub

-- L02
#check EfficientFFA.LazyArithmetic.bounded_sub

-- L02
#check EfficientFFA.LazyArithmetic.represents_sub

-- L03
#check EfficientFFA.LazyArithmetic.eval_neg

-- L03
#check EfficientFFA.LazyArithmetic.bounded_neg

-- L03
#check EfficientFFA.LazyArithmetic.represents_neg

-- L04
#check EfficientFFA.LazyArithmetic.bounded_add_constant

-- L04
#check EfficientFFA.LazyArithmetic.represents_add_constant

-- L05
#check EfficientFFA.eval_scale

-- L05
#check EfficientFFA.LazyArithmetic.bounded_scale

-- L05
#check EfficientFFA.LazyArithmetic.represents_scale

-- L06
#check EfficientFFA.LazyArithmetic.represents_reduced

-- L06
#check EfficientFFA.Normalization.Parameters.stored_normalization_sound

-- L06, L10
#check EfficientFFA.Normalization.Parameters.stored_normalization_exists

-- L06
#check EfficientFFA.Normalization.Parameters.subtraction_normalization_sound

-- L07
#check EfficientFFA.Normalization.residual_mod

-- L07
#check EfficientFFA.Normalization.residual_dvd_iff

-- L07
#check EfficientFFA.Normalization.normalization_iff_quotient

-- L08
#check EfficientFFA.Normalization.weighted_linear_bounds

-- L08
#check EfficientFFA.Normalization.Parameters.residual_bounds

-- L09
#check EfficientFFA.Normalization.Parameters.auxCore_congr

-- L09
#check EfficientFFA.Normalization.Parameters.auxCore_bounds

-- L09
#check EfficientFFA.Normalization.Parameters.nativeResidual_bounds

-- L09
#check EfficientFFA.Normalization.Parameters.auxResidual_bounds

-- L09
#check EfficientFFA.Normalization.Parameters.normalization_sound

-- L09
#check EfficientFFA.Normalization.Parameters.normalization_complete

-- L09
#check EfficientFFA.Normalization.Parameters.accepts_iff_normalization

-- L10
#check EfficientFFA.Normalization.Parameters.normalization_exists

-- D01
#check EfficientFFA.Division.inverse_exists_iff_coprime

-- D01
#check EfficientFFA.Division.division_iff

-- D01
#check EfficientFFA.Division.encoded_division_iff

-- D01
#check EfficientFFA.Division.encoded_inverse_iff

-- D02
#check EfficientFFA.Division.prime_inverse_iff

-- D02
#check EfficientFFA.Division.prime_disequality_iff

-- D02
#check EfficientFFA.Native.ECEncoding.distinct_iff

-- Z01
#check EfficientFFA.ShiftedEncoding.value

-- Z01
#check EfficientFFA.ShiftedEncoding.zero_iff_eval

-- Z01
#check EfficientFFA.ShiftedEncoding.exists_unique_zero

-- Z01
#check EfficientFFA.ShiftedEncoding.zero_iff_limbs

-- Z02
#check EfficientFFA.ShiftedEncoding.exists_representation

-- Z03
#check EfficientFFA.ShiftedEncoding.zero_iff_native_checks

-- Z04
#check EfficientFFA.ShiftedEncoding.Multiplication.shifted_product_identity

-- Z04
#check EfficientFFA.ShiftedEncoding.Multiplication.residual_mod

-- Z04
#check EfficientFFA.ShiftedEncoding.Multiplication.multiplication_iff_quotient

-- Z04
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.residual_bounds

-- Z04
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.auxCore_bounds

-- Z04
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.nativeResidual_bounds

-- Z04
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.auxResidual_bounds

-- Z05
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.auxCore_congr

-- Z05
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.multiplication_sound

-- Z05
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.multiplication_complete

-- Z05
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.accepts_iff_multiplication

-- Z05
#check EfficientFFA.ShiftedEncoding.Multiplication.Parameters.multiplication_exists

-- Z06
#check EfficientFFA.ShiftedEncoding.value_congr_iff

-- Z06
#check EfficientFFA.ShiftedEncoding.normalization_iff

-- Z06
#check EfficientFFA.ShiftedEncoding.stored_normalization_sound

-- Z06
#check EfficientFFA.ShiftedEncoding.stored_normalization_exists

-- Z07
#check EfficientFFA.ShiftedEncoding.eval_bump

-- Z07
#check EfficientFFA.ShiftedEncoding.value_add

-- Z07
#check EfficientFFA.ShiftedEncoding.value_sub

-- Z07
#check EfficientFFA.ShiftedEncoding.value_neg

-- Z07
#check EfficientFFA.ShiftedEncoding.value_add_constant

-- Z07
#check EfficientFFA.ShiftedEncoding.value_scale

-- Z07
#check EfficientFFA.ShiftedEncoding.bounded_add

-- Z07
#check EfficientFFA.ShiftedEncoding.bounded_sub

-- Z07
#check EfficientFFA.ShiftedEncoding.bounded_neg

-- Z07
#check EfficientFFA.ShiftedEncoding.bounded_scale

-- E01
#check EfficientFFA.EllipticCurve.Curve

-- E01
#check EfficientFFA.EllipticCurve.Curve.equation_iff

-- E01
#check EfficientFFA.EllipticCurve.Curve.nonsingular

-- E01
#check EfficientFFA.EllipticCurve.Curve.point

-- E01
#check EfficientFFA.EllipticCurve.Curve.point_ne_zero

-- E01
#check EfficientFFA.EllipticCurve.Curve.point_injective

-- E02, E07
#check EfficientFFA.Native.GateKind.expression

-- E02
#check EfficientFFA.Native.ECEncoding.onCurve_iff

-- E03
#check EfficientFFA.EllipticCurve.chord

-- E03
#check EfficientFFA.EllipticCurve.AddChecks

-- E03
#check EfficientFFA.EllipticCurve.add_checks_iff

-- E03, E12
#check EfficientFFA.Native.ECEncoding.add_iff

-- E04
#check EfficientFFA.EllipticCurve.tangent

-- E04
#check EfficientFFA.EllipticCurve.DoubleChecks

-- E04
#check EfficientFFA.EllipticCurve.double_checks_iff

-- E04
#check EfficientFFA.EllipticCurve.Curve.double_den_ne

-- E04, E12
#check EfficientFFA.Native.ECEncoding.double_iff

-- E05
#check EfficientFFA.EllipticCurve.result

-- E05, O02
#check EfficientFFA.EllipticCurve.output_determined

-- E05
#check EfficientFFA.EllipticCurve.Curve.result_group

-- E05, O03
#check EfficientFFA.EllipticCurve.Curve.addition_sound

-- E05
#check EfficientFFA.EllipticCurve.Curve.doubling_sound

-- E06
#check EfficientFFA.Native.Polynomial.reduce_congr

-- E06
#check EfficientFFA.Native.Polynomial.eval_bounds

-- E06
#check EfficientFFA.Native.Parameters.residual_congr

-- E06
#check EfficientFFA.Native.Parameters.residual_bounds

-- E06
#check EfficientFFA.Native.Parameters.auxCore_bounds

-- E06
#check EfficientFFA.Native.Parameters.auxCore_congr

-- E06
#check EfficientFFA.Native.Parameters.sound

-- E06
#check EfficientFFA.Native.Parameters.accepts_iff

-- E06, E07
#check EfficientFFA.Native.Expression.compile_eval

-- E06
#check EfficientFFA.Native.Expression.checks_iff

-- E06
#check EfficientFFA.Native.ECEncoding.check_iff

-- E08
#check EfficientFFA.Native.bit_cases

-- E08
#check EfficientFFA.Native.Parameters.Activated

-- E08
#check EfficientFFA.Native.Parameters.activated_sound

-- E08
#check EfficientFFA.Native.Parameters.activated_one

-- E08
#check EfficientFFA.Native.Parameters.activated_zero

-- E10
#check EfficientFFA.EllipticCurve.Encoded

-- E10
#check EfficientFFA.EllipticCurve.Curve.Valid

-- E10
#check EfficientFFA.EllipticCurve.Curve.decode

-- E10
#check EfficientFFA.EllipticCurve.Curve.decode_finite

-- E10
#check EfficientFFA.EllipticCurve.Curve.decode_infinity

-- E10
#check EfficientFFA.Native.ECEncoding.flag_iff

-- E11
#check EfficientFFA.Subgroup.mem_iff_card_nsmul_eq_zero

-- E11
#check EfficientFFA.Native.ECEncoding.member_iff

-- E11
#check EfficientFFA.EllipticCurve.Curve.trace_output_mem_subgroup

-- E11
#check EfficientFFA.Native.ECEncoding.trace_output_mem_subgroup

-- O01
#check EfficientFFA.EllipticCurve.Curve.DoubleAccepts

-- O01
#check EfficientFFA.EllipticCurve.Curve.flagged_double_sound

-- O01
#check EfficientFFA.EllipticCurve.Curve.flagged_double_complete

-- O01, O02
#check EfficientFFA.EllipticCurve.Curve.flagged_double_witnesses_iff

-- O01
#check EfficientFFA.EllipticCurve.Curve.flagged_double_complete_of_no_two_torsion

-- O03
#check EfficientFFA.EllipticCurve.Curve.IncompleteAccepts

-- O03
#check EfficientFFA.EllipticCurve.Curve.incomplete_sound

-- O03
#check EfficientFFA.EllipticCurve.Curve.incomplete_complete

-- O03
#check EfficientFFA.EllipticCurve.Curve.addition_complete

-- O04, O06
#check EfficientFFA.EllipticCurve.Curve.CompleteAccepts

-- O04
#check EfficientFFA.EllipticCurve.Curve.complete_sound

-- O04
#check EfficientFFA.EllipticCurve.Curve.complete_exists

-- O04
#check EfficientFFA.EllipticCurve.Curve.complete_correct

-- O04
#check EfficientFFA.Native.ECEncoding.complete_iff

-- O05
#check EfficientFFA.EllipticCurve.IdentityCopies

-- O05
#check EfficientFFA.EllipticCurve.identity_copies_iff

-- O05
#check EfficientFFA.Native.ECEncoding.copy_iff

-- O05
#check EfficientFFA.Native.ECEncoding.encodedCopy_iff

-- O06
#check EfficientFFA.Tests.PaperAudit.single_infinity_literal_conflict

-- T01
#check EfficientFFA.MSM.entry

-- T01
#check EfficientFFA.MSM.entry_succ

-- T01, T02
#check EfficientFFA.EllipticCurve.Curve.table_sound

-- T01, T06
#check EfficientFFA.EllipticCurve.Curve.table_lookup_sound

-- T02
#check EfficientFFA.EllipticCurve.x_ne_of_add_checks

-- T02
#check EfficientFFA.EllipticCurve.Curve.repeated_step

-- T02
#check EfficientFFA.EllipticCurve.Curve.table_guards

-- T02
#check EfficientFFA.EllipticCurve.Curve.table_safe

-- T03
#check EfficientFFA.MSM.TableSafe

-- T03
#check EfficientFFA.EllipticCurve.Curve.table_complete

-- T03
#check EfficientFFA.MSM.table_safe_iff_avoids

-- T03
#check EfficientFFA.MSM.badOffsets_card_le

-- T04
#check EfficientFFA.MSM.badSeeds_card_le

-- T04
#check EfficientFFA.MSM.exists_safe_setup_prime

-- T04
#check EfficientFFA.EllipticCurve.Curve.tables_exist_of_parameters

-- T05
#check EfficientFFA.EllipticCurve.Curve.scale_sound

-- T05
#check EfficientFFA.EllipticCurve.Curve.scale_exists

-- T05
#check EfficientFFA.EllipticCurve.Curve.trace_setup

-- T05
#check EfficientFFA.Native.ECEncoding.scale_iff

-- T05
#check EfficientFFA.Native.ECEncoding.trace_iff

-- T06
#check EfficientFFA.EllipticCurve.Curve.trace_lookup

-- T06
#check EfficientFFA.MSM.descending_range

-- T07
#check EfficientFFA.MSM.addRows_eq

-- T07
#check EfficientFFA.MSM.loop_invariant

-- T07
#check EfficientFFA.MSM.row_invariant

-- T07
#check EfficientFFA.MSM.rowValue

-- T07
#check EfficientFFA.MSM.offsetCoeff

-- T07
#check EfficientFFA.EllipticCurve.Curve.trace_rows

-- T07
#check EfficientFFA.EllipticCurve.Curve.trace_boundaries

-- T08
#check EfficientFFA.MSM.horner_eq_sum

-- T08
#check EfficientFFA.MSM.descending

-- T08
#check EfficientFFA.MSM.loop_correct

-- T08, T10
#check EfficientFFA.EllipticCurve.Curve.trace_sound_littleEndian

-- T08, T10
#check EfficientFFA.Native.ECEncoding.trace_sound_littleEndian

-- T09
#check EfficientFFA.MSM.addRows_ne_zero

-- T09
#check EfficientFFA.MSM.loop_ne_zero

-- T09
#check EfficientFFA.MSM.row_ready

-- T09
#check EfficientFFA.MSM.doubling_ready

-- T09, T13
#check EfficientFFA.EllipticCurve.Curve.trace_complete

-- T10
#check EfficientFFA.EllipticCurve.Curve.trace_sound

-- T11
#check EfficientFFA.MSM.collision_iff

-- T11
#check EfficientFFA.MSM.collision_coeff_bounds

-- T11
#check EfficientFFA.MSM.collisionSeeds_card_le

-- T11
#check EfficientFFA.MSM.loopBadSeeds_card_le_prime

-- T12
#check EfficientFFA.MSM.failureBudget

-- T12
#check EfficientFFA.MSM.uniform_group_failure_bound_prime

-- T12
#check EfficientFFA.EllipticCurve.Curve.uniform_littleEndian_trace_failure_bound_prime

-- T12
#check EfficientFFA.Native.ECEncoding.uniform_littleEndian_failure_bound

-- T13
#check EfficientFFA.EllipticCurve.Curve.TraceWitnesses

-- T13
#check EfficientFFA.Native.ECEncoding.traceWitnesses_iff

-- T13
#check EfficientFFA.Native.ECEncoding.exists_correct_trace

-- T14
#check EfficientFFA.MSM.groupAccepts_map_iff

-- T14
#check EfficientFFA.EllipticCurve.Curve.trace_complete_subgroup

-- T14
#check EfficientFFA.Native.ECEncoding.uniform_subgroup_failure_bound

-- T14
#check EfficientFFA.Native.ECEncoding.uniform_subgroup_failure_bound_checked

-- T14
#check EfficientFFA.Native.ECEncoding.exists_correct_subgroup_trace

-- T16
#check EfficientFFA.EllipticCurve.Curve.point_opposite

-- T16
#check EfficientFFA.EllipticCurve.Curve.coordinates_neg

-- T16
#check EfficientFFA.Native.ECEncoding.opposite_iff

-- I03
#check EfficientFFA.Native.ECEncoding


-- E08, O04, O05: native selectors and shared coordinate limbs
#check EfficientFFA.Native.ECEncoding.CompleteConstraints
#check EfficientFFA.Native.ECEncoding.completeConstraints_sound
#check EfficientFFA.Native.ECEncoding.completeCircuit_iff
#check EfficientFFA.Native.ECEncoding.completeCircuit_sound
#check EfficientFFA.Native.ECEncoding.completeCircuit_complete
#check EfficientFFA.Native.ECEncoding.copyLimbs_one_iff
