# Paper coverage across the two formalizations

This guide links corresponding mathematical endpoints in the two independently
developed formalizations. It is a navigation and assumption comparison, not a
proof that the developments are equivalent or have identical coverage. No
mathematical statement was changed during the repository migration.

The detailed [paper-to-Lean inventory](../lean/PAPER_RESULTS_MAP.md) contains
90 claim-family entries; IDs below refer to that inventory. The
[EasyCrypt repair/status record](../easycrypt/FORMALIZATION_REPAIR_PLAN.md)
provides its historical context and validation boundaries. Short Lean prefixes
(A, M, L, N, D, S, SM, C, E, X, MSM) are expanded in the detailed inventory;
each link goes directly to the declaration. Definitions are distinguished
from theorem endpoints in that inventory.

| Paper result | EasyCrypt endpoint | Lean endpoint | Assumptions and differences |
|---|---|---|---|
| LCM reconstruction (§1.2; F01–F02) | [LCM_divides](../easycrypt/IntegerLCM.ec#L54), [LCM_congruence](../easycrypt/IntegerLCM.ec#L90) | [A.congruent_all_iff_lcm](../lean/EfficientFFA/Arithmetic.lean#L19), [A.eq_zero_of_congruences_of_bounds](../lean/EfficientFFA/Arithmetic.lean#L43) | Both use actual LCM divisibility; pairwise coprimality is unnecessary. Finite collections and signed-bound conventions differ. |
| Multiplication soundness (Theorem 3.1; M10) | [multiplication_soundness](../easycrypt/FFA_soundness.ec#L149) | [M.multiplication_sound](../lean/EfficientFFA/Multiplication/Soundness.lean#L16) | EasyCrypt uses its word/array limb theories; Lean uses integer limbs with explicit WellFormed premises. Both require suitable parameter and no-wrap conditions. |
| Multiplication completeness (Theorem 3.2; M11) | [multiplication_completeness](../easycrypt/FFA_completeness.ec#L14) | [M.multiplication_complete](../lean/EfficientFFA/Multiplication/Completeness.lean#L53) | Both construct quotient witnesses. Compare quotient rounding and width definitions before transferring parameter choices; the Lean map records the auxiliary upper-rounding refinement (M04). |
| Lazy arithmetic and normalization (§3.2; L01–L10) | No corresponding endpoint identified. | [L.bounded_add](../lean/EfficientFFA/LazyArithmetic.lean#L14), [L.represents_sub](../lean/EfficientFFA/LazyArithmetic.lean#L62), [N.normalization_sound](../lean/EfficientFFA/Normalization/Soundness.lean#L16), [N.normalization_complete](../lean/EfficientFFA/Normalization/Completeness.lean#L54), [N.stored_normalization_exists](../lean/EfficientFFA/Normalization.lean#L59) | Lean supplies signed bounds, stored-residue transport and normalization gates. EasyCrypt limb utilities are not a corresponding proved normalization-gate interface. |
| Foreign-field division and disequality (§§3.2.2–3.2.3; D01–D02) | No corresponding endpoint identified. | [D.encoded_division_iff](../lean/EfficientFFA/Division.lean#L61), [D.prime_disequality_iff](../lean/EfficientFFA/Division.lean#L55) | Lean separates unit/coprimality conditions from the prime-field nonzero criterion. Inverses used inside EasyCrypt EC formulas do not constitute this generic foreign-field interface. |
| Unique-zero shifted encoding (§3.2.4; Z01–Z07) | No corresponding endpoint identified. | [S.zero_iff_native_checks](../lean/EfficientFFA/ShiftedEncoding/Representation.lean#L63), [SM.accepts_iff_multiplication](../lean/EfficientFFA/ShiftedEncoding/Multiplication.lean#L7), [S.normalization_iff](../lean/EfficientFFA/ShiftedEncoding/Arithmetic.lean#L116) | Lean proves shifted arithmetic separately. Neither development currently supplies the complete shifted EC/native-trace composition described as a possible adaptation. |
| Affine incomplete addition (Equations 7, 9; Figure 2) | [affine_witness_exists](../easycrypt/AffineAddition.ec#L41), [affine_equations_unique](../easycrypt/AffineAddition.ec#L83), [affine_equations_on_curve](../easycrypt/AffineAddition.ec#L162) | [C.addition_sound](../lean/EfficientFFA/EllipticCurve/GroupLaw.lean#L58), [C.addition_complete](../lean/EfficientFFA/EllipticCurve/GroupLaw.lean#L65) | EasyCrypt proves modular coordinate-formula facts and uses explicit coordinate/group-model contracts for generic MSM composition. Lean connects coordinates to mathlib’s concrete smooth-curve group. Distinct input x-coordinates are required or derived. |
| Doubling (Equation 8; Figure 1) | [doubling_witness_exists](../easycrypt/AffineDoubling.ec#L45), [doubling_equations_unique](../easycrypt/AffineDoubling.ec#L55) | [C.doubling_sound](../lean/EfficientFFA/EllipticCurve/GroupLaw.lean#L87), [C.flagged_double_witnesses_iff](../lean/EfficientFFA/EllipticCurve/Flagged.lean#L55) | The finite tangent denominator must be nonzero for witness existence. Lean gives the precise flagged condition; no order-three exclusion is needed by its coordinate-output proof. |
| Complete addition (Figure 3; O04–O06) | [complete_constraints_sound](../easycrypt/AffineComplete.ec#L117), [complete_witness_exists](../easycrypt/AffineComplete.ec#L87) | [C.complete_correct](../lean/EfficientFFA/EllipticCurve/Complete.lean#L76), [E.complete_iff](../lean/EfficientFFA/Native/Trace.lean#L47) | Both use ordered case distinctions. Lean additionally proves [E.completeCircuit_iff](../lean/EfficientFFA/Native/CompleteCircuit.lean), with native selector checks and shared limb wires (native prime, B≤p, valid inputs). The recorded paper proposal makes the branches disjoint; both the current LaTeX and original PDF remain unchanged. Infinity-coordinate and representation conventions must be compared explicitly. |
| Table equations imply internal guards (§4.5; T01–T02) | [accepted_step_distinct_x](../easycrypt/MSM_TableConstraints.ec#L191), [accepted_table_entries](../easycrypt/MSM_TableConstraints.ec#L135) | [C.table_guards](../lean/EfficientFFA/MSM/Tables.lean#L89), [C.table_sound](../lean/EfficientFFA/MSM/Tables.lean#L68) | Accepted equations plus initial/base conditions imply the internal checks; this does not add per-entry guards. This soundness statement is distinct from existence of table witnesses for arbitrary seeds. |
| Table witness construction (§4.5; T03–T04) | [table_build_spec](../easycrypt/MSM_TableConstruction.ec#L129), [safe_table_has_witnesses](../easycrypt/MSM_CoordinateWitnesses.ec#L141) | [C.table_complete](../lean/EfficientFFA/MSM/Tables.lean#L142), [C.tables_exist_of_parameters](../lean/EfficientFFA/MSM/Parameters.lean#L101) | Safe-offset/admissibility hypotheses are essential. Parameter selection and rejection analysis address unsuitable seeds such as the known V=2P example. |
| Little-endian scalar meaning (Figure 4; T08) | [reversed_core_spec](../easycrypt/MSM_WindowOrder.ec#L56), [little_endian_msm_soundness](../easycrypt/MSM_WindowOrder.ec#L90) | [MSM.loop_correct](../lean/EfficientFFA/MSM/Loop.lean#L68), [C.trace_sound_littleEndian](../lean/EfficientFFA/MSM/Trace.lean#L151) | EasyCrypt reverses windows before its big-endian core. Lean traverses little-endian windows in descending order. Both differ from the printed forward traversal paired with a little-endian expansion. |
| Full coordinate-trace soundness (§4.5; T05–T10) | [little_endian_full_sound](../easycrypt/MSM_FullCoordinates.ec#L153) | [C.trace_sound_littleEndian](../lean/EfficientFFA/MSM/Trace.lean#L151) | Both link setup, tables, loop and final correction. EasyCrypt assumes coordinate_laws and complete_affine_model over its abstract group; Lean uses actual curve points. These are related contracts, not a proved cross-language equivalence. |
| Normalized rejection probability (§4.5; T11–T13) | [sampled_rejection_bound_cardinality](../easycrypt/MSM_RejectionBound.ec#L249), [little_endian_full_failure_bound](../easycrypt/MSM_FullCoordinates.ec#L163) | [C.uniform_littleEndian_trace_failure_bound_prime](../lean/EfficientFFA/MSM/TraceStatistics.lean#L41), [E.uniform_littleEndian_failure_bound](../lean/EfficientFFA/Native/Statistics.lean#L21) | Both obtain (1+l*(2^w+1)+2*T*l)/N. EasyCrypt carries abstract group/scalar assumptions and explicit full, uniform, lossless sampler assumptions. Lean uses a normalized finite uniform PMF and explicit prime-order/numerical hypotheses. Full/uniform alone are not substituted for losslessness. |
| Native encoding of EC identities and traces (§4.1; E02–E08, T10) | No corresponding endpoint identified. | [X.compile_eval](../lean/EfficientFFA/Native/Expression.lean#L57), [E.onCurve_iff](../lean/EfficientFFA/Native/EllipticCurve.lean#L91), [E.trace_iff](../lean/EfficientFFA/Native/Trace.lean#L116), [E.trace_sound_littleEndian](../lean/EfficientFFA/Native/Trace.lean#L157) | Lean composes bounded native polynomial encodings with EC/MSM semantics. EasyCrypt’s separate FFA and coordinate results do not provide that native-limb composition endpoint. The separate Lean complete-add gadget now fixes shared limbs and checks selector dispatch. Whole-trace shared wiring and a complete PLONK layout remain unverified. |
| Prime-order subgroup support (§4.2; E11, T14) | No corresponding endpoint identified. | [E.member_iff](../lean/EfficientFFA/Native/Subgroup.lean#L24), [E.uniform_subgroup_failure_bound](../lean/EfficientFFA/Native/Subgroup.lean#L38), [E.uniform_subgroup_failure_bound_checked](../lean/EfficientFFA/Native/Subgroup.lean#L67) | EasyCrypt’s abstract group can model an appropriate group, but has no counterpart to Lean’s ambient-curve subgroup wrappers and checked membership interface. The latter’s annihilation test needs coprime cofactor; sampling assumes uniformity inside the subgroup. |
| Small concrete validation instances (extensions) | [concrete_iff](../easycrypt/SmallFFA.ec#L156), [concrete_failure_bound](../easycrypt/SmallMSM.ec#L34) | See linked instance files. | EasyCrypt supplies q=13 multiplication and a seven-point curve over F5 with a 6/7 MSM failure bound. Lean supplies [Curve17](../lean/EfficientFFA/Instances/Curve17.lean) and [Subgroup17](../lean/EfficientFFA/Instances/Subgroup17.lean). These are different validation examples, not matching production instantiations. |
| Production parameters, GLV, applications and measurements (§6; T15, P01–P12) | Outside the verified scope. | Outside the verified scope. | Neither library verifies the reported Halo2 circuit implementation, GLV optimization, ECDSA/recursive proof-system applications, resource counts or benchmarks. Production parameter instances remain deferred. |

## Reading the guarantees

Both developments prove results under explicit parameter and representation
contracts. A successful generic proof is not proof that every proposed
parameter set meets those contracts. The small instances discharge particular
choices; they do not validate the paper’s production tables.

EasyCrypt’s generic development uses abstract algebra and sampler assumptions,
with concrete instances discharging the relevant project obligations. Its
local checker trusts the supplied standard library and uses external SMT
solvers. Lean uses mathlib and kernel-checked proofs; its theorem dependency
reports use the standard Lean axioms. These are different trust boundaries.

Combining their source trees does not change the independent-development
policy recorded in [lean/README.md](../lean/README.md). No supplied external
Lean artifact or archive was consulted for this migration.

## Current-source theorem and review follow-up

The older pinned PDF has two numbered multiplication theorems. The LaTeX
source at paper baseline `39ae3d0` adds an MSM theorem; inventory T17 now maps
it to the soundness and normalized failure-bound endpoints above. The separate
`review/formalization-alignment` branch records unapplied proposals in
`PAPER_REVISION_PROPOSALS.txt` for its unconditional wording, window traversal,
Figure 3 branches and arithmetic qualifications. The LaTeX is unchanged. The
historical PDF/release provenance is retained. Production instances and full
MSM shared-wire/circuit implementation remain outside this milestone.
