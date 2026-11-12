# Independent Lean formalization of efficient foreign-field arithmetic

This independently developed library formalizes the arithmetic and EC/MSM
constraint relations in [Efficient Foreign-Field Arithmetic in PLONK](https://eprint.iacr.org/2025/695).
The reviewed paper revision is
[dddacd0](https://github.com/miguel-ambrona/ffa-paper/tree/dddacd019ef180c1c6f1bfa06359bd59bf8c6733);
the reviewed Lean proof artifact is
[91aa985](https://github.com/input-output-hk/efficient-ffa/tree/91aa985ffdbdfa604e9b75d9af07981ee416c3f1/lean).

The [paper results map](PAPER_RESULTS_MAP.md) links all 92 claim families to
current paper locations, Lean declarations and explicit assumptions. It includes
the five theorem statements, production arithmetic certificates, normalization
limits, shifted identities and MSM statistical conditions. The independent
review found no new substantive mathematical defect within that theoretical scope.

[EfficientFFA/Paper.lean](EfficientFFA/Paper.lean) exposes the headline contracts;
[Paper/MSMContract.lean](EfficientFFA/Paper/MSMContract.lean) combines MSM soundness,
the finite rejection bound and conditional witness existence. Whole-MSM shared
wiring, PLONK/Halo2 implementation, GLV, benchmarks and application/security
proofs remain outside scope. A separate complete-add gadget checks native
selectors and shares limb wires across its gates.

## Build and trust boundary

Run from this directory:

~~~sh
lake exe cache get
lake build
~~~

Lean is pinned to 4.31.0 and mathlib to
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. The manifest also pins transitive
dependencies. The cache command fetches mathlib artifacts for a fresh checkout.
The default build checks the library and regressions with warnings as errors;
it is not a fresh rebuild of mathlib. CI remains outside scope.

All 477 library theorems compile. Eight additional dependency reports cover
encoding constructors. The 485 reports contain only Lean's standard propext,
Classical.choice and Quot.sound axioms, or a subset. There are no project
axioms, admissions or native_decide proofs.

## Mathematical contracts

- Multiplication and normalization check native congruences, bounded quotient
  witnesses and explicit auxiliary equations. No-wrap conditions establish
  soundness; sufficient widths establish completeness. Capacity supplies an
  output representation. Bounded limbs need not be canonical residues.
- Lazy operations preserve independently tracked signed integer limbs through
  native residues. Normalization uses the tracked bounds. The ten production
  arithmetic configurations include explicit supported normalization limits.
- Shifted encoding interprets limbs as 1 plus their radix sum. Unique zero
  requires q≤B^n<2q; native limb zero tests additionally require B≤p. Shifted
  coordinate identities have separate bounds and witnesses; the MSM trace
  uses the ordinary encoding.
- Coordinate equations connect to mathlib's smooth-curve group. Complete
  addition uses ordered identity, inverse, doubling and distinct-x branches.
  Finite doubling witnesses require 2y≠0; soundness derives this from accepted
  tangent equations and nonsingularity. No order-three exclusion is needed.
- Accepted table recurrences derive internal incomplete-addition preconditions
  from valid base/start points and the initial guard. Suitable-offset witness
  existence is separate; no per-entry table guards are added.
- MSM processes little-endian windows in descending order. Setup scalar links
  use complete-addition chains. For fixed inputs and a uniform seed in a
  prime-order group/subgroup of order N, including its identity, the failure
  bound is (1+l*(2^w+1)+2*T*l)/N under the stated size conditions. Existence
  additionally requires that numerator to be below N.
- Subgroup loading via [N]P=0 requires the coprime-cofactor condition. Numerical
  production certificates prove arithmetic inequalities, not large-field
  primality or curve/subgroup orders. The small curve and subgroup examples
  discharge combined arithmetic and statistical assumptions.

## Checked modules and regressions

| File | Result |
|---|---|
| [ShiftedEncoding/Expression.lean](EfficientFFA/ShiftedEncoding/Expression.lean) | Shifted polynomial compilation, evaluation, residual bounds and explicit quotient witnesses |
| [ShiftedEncoding/EllipticCurve.lean](EfficientFFA/ShiftedEncoding/EllipticCurve.lean) | Shifted native EC identities and group-level addition/doubling correctness; unique zero under its separate capacity condition |
| [Paper/MSMContract.lean](EfficientFFA/Paper/MSMContract.lean) | Consolidated soundness, statistical failure bound and conditional trace-existence contracts |
| [Paper/Rounding.lean](EfficientFFA/Paper/Rounding.lean) | Truncation-to-floor width compatibility at unchanged widths and actual no-wrap conditions |
| [Paper/Arithmetic.lean](EfficientFFA/Paper/Arithmetic.lean) | Duplicate residue classification, precise radix headroom, accumulation/scaling bounds, weighted-bound comparison and normalization interval transport |
| [Instances/PaperParameters.lean](EfficientFFA/Instances/PaperParameters.lean) | Ten production arithmetic settings: capacity, multiplication, nine EC identities and normalization with the same moduli; exact limits in the claim map |
| [Paper.lean](EfficientFFA/Paper.lean) | Paper-facing multiplication, normalization, ordered complete addition and MSM soundness/statistical-completeness contracts |
| [Arithmetic.lean](EfficientFFA/Arithmetic.lean) | A concrete finite LCM, equivalence with simultaneous congruences, and bounded reconstruction |
| [Limbs.lean](EfficientFFA/Limbs.lean) | Integer limb evaluation, product expansion, modular coefficient reduction, quotient characterization, reconstruction corollary, and integer linearity |
| [Multiplication/Definitions.lean](EfficientFFA/Multiplication/Definitions.lean) | Concrete parameters, coefficient reductions, quotient shifts, ranges, and native-modulus checks |
| [Multiplication/Bounds.lean](EfficientFFA/Multiplication/Bounds.lean) | Weighted-sum bounds, signed quotient intervals, and all four residual bounds |
| [Multiplication/Soundness.lean](EfficientFFA/Multiplication/Soundness.lean) | Auxiliary coefficient correspondence and soundness of the actual constraints |
| [Multiplication/Completeness.lean](EfficientFFA/Multiplication/Completeness.lean) | Explicit quotient witnesses, their ranges, and completeness |
| [Multiplication.lean](EfficientFFA/Multiplication.lean) | Acceptance iff modular multiplication, and canonical-output corollary |
| [Multiplication regressions](Tests/Multiplication.lean) | Full small parameter instances, explicit witnesses, rounding, noncanonical outputs, and incomplete-check counterexample |
| [LazyArithmetic.lean](EfficientFFA/LazyArithmetic.lean) | All five Table 1 bound rules, preservation of native-residue representation, and uniqueness of lifts in short intervals |
| [Representation.lean](EfficientFFA/Representation.lean) | Bounded limb representations, capacity bounds, and injectivity of integer evaluation |
| [Normalization.lean](EfficientFFA/Normalization.lean) and its submodules | Linear residual bounds, actual auxiliary checks, soundness, explicit witnesses, canonical output existence, and stored-residue transport |
| [Division.lean](EfficientFFA/Division.lean) | Invertibility criterion, encoded division/inversion, and prime-modulus inverse-of-difference criterion |
| [Lazy/normalization regressions](Tests/LazyNormalization.lean) | Signed native wraparound, full parameters and witnesses, interval endpoints, wrong-output rejection, capacity failure, and composite-modulus counterexamples |
| [ShiftedEncoding/Representation.lean](EfficientFFA/ShiftedEncoding/Representation.lean) | Unique zero, shifted representability, and integer/native limb zero tests |
| [ShiftedEncoding/Arithmetic.lean](EfficientFFA/ShiftedEncoding/Arithmetic.lean) | Corrected operations, signed bounds, native representation, and reuse of normalization |
| [ShiftedEncoding/Multiplication.lean](EfficientFFA/ShiftedEncoding/Multiplication.lean) and its submodules | Revised residual bounds, encoded soundness/completeness, and output/witness existence |
| [Shifted regressions](Tests/ShiftedEncoding.lean) | Uniqueness boundaries, native aliasing, corrected operations, and full shifted multiplication instances |
| [EllipticCurve/Affine.lean](EfficientFFA/EllipticCurve/Affine.lean) | Smooth short Weierstrass curves and the paper's affine coordinate constraints |
| [EllipticCurve/GroupLaw.lean](EfficientFFA/EllipticCurve/GroupLaw.lean) | Connection to mathlib's concrete curve group; addition/doubling soundness and witnesses |
| [EllipticCurve/Flagged.lean](EfficientFFA/EllipticCurve/Flagged.lean) | Infinity-tagged operations, exact doubling completeness condition, and literal identity-copy limitation |
| [EllipticCurve/Complete.lean](EfficientFFA/EllipticCurve/Complete.lean) | Explicitly ordered complete-add refinement, sound and complete for all valid pairs |
| [MSM/Tables.lean](EfficientFFA/MSM/Tables.lean) | Accepted repeated-base equations imply internal guards, curve membership, and lookup meaning; admissible offsets yield affine witnesses |
| [MSM/TableOffsets.lean](EfficientFFA/MSM/TableOffsets.lean) | Exact excluded-offset set and its cardinality bound |
| [MSM/Parameters.lean](EfficientFFA/MSM/Parameters.lean) | Seed exclusion bound, suitable-seed existence from coprimality/cardinality, and actual affine table witnesses |
| [MSM/Loop.lean](EfficientFFA/MSM/Loop.lean) | Executable group recurrence, offset invariants, and corrected little-endian MSM result |
| [MSM/Collisions.lean](EfficientFFA/MSM/Collisions.lean) | Actual loop collision equations, coefficient bounds, and at most two excluded seeds per addition |
| [MSM/Rejection.lean](EfficientFFA/MSM/Rejection.lean) | Combined exclusion budget, normalized uniform failure bound, and prime-parameter existence theorem |
| [MSM/Safety.lean](EfficientFFA/MSM/Safety.lean) | Nonidentity intermediate states and local affine addition/doubling witnesses |
| [MSM/Chains.lean](EfficientFFA/MSM/Chains.lean) | Complete-add chains enforce seed-to-constant multiplication linkage |
| [MSM/Trace.lean](EfficientFFA/MSM/Trace.lean) | Coordinate-only full trace acceptance and soundness for arbitrary supplied witnesses |
| [MSM/TraceCompleteness.lean](EfficientFFA/MSM/TraceCompleteness.lean) | Construction of a full linked coordinate trace from every successful group execution |
| [MSM/TraceStatistics.lean](EfficientFFA/MSM/TraceStatistics.lean) | Statistical completeness and correct-trace existence under explicit prime-group parameters |
| [Native/Polynomial.lean](EfficientFFA/Native/Polynomial.lean) and [Native/Gate.lean](EfficientFFA/Native/Gate.lean) | Sparse polynomial bounds, signed coefficient reductions, actual native/auxiliary checks, soundness and quotient witnesses |
| [Native/Expression.lean](EfficientFFA/Native/Expression.lean) and [Native/Activation.lean](EfficientFFA/Native/Activation.lean) | Limb compilation, foreign-field representation, native bitness, enabled and disabled gates |
| [Native/EllipticCurve.lean](EfficientFFA/Native/EllipticCurve.lean) | Encodings of (6)–(9), checked square linkage, copies, and inverse-of-difference certificates |
| [Native/Trace.lean](EfficientFFA/Native/Trace.lean) and [Native/Statistics.lean](EfficientFFA/Native/Statistics.lean) | Native arithmetic trace equivalence, MSM soundness, and native-witness statistical completeness |
| [EllipticCurve/Cardinality.lean](EfficientFFA/EllipticCurve/Cardinality.lean) and [Instances/Curve17.lean](EfficientFFA/Instances/Curve17.lean) | Actual curve-group enumeration, 19-point cardinality, valid EC encoding and instantiated 8/19 bound |
| [MSM/Embedding.lean](EfficientFFA/MSM/Embedding.lean) and [MSM/Subgroup.lean](EfficientFFA/MSM/Subgroup.lean) | Group embedding correspondence, subgroup-only radix injectivity, coordinate witness existence, uniform subgroup failure bound and output membership |
| [EllipticCurve/Subgroup.lean](EfficientFFA/EllipticCurve/Subgroup.lean) and [Native/Subgroup.lean](EfficientFFA/Native/Subgroup.lean) | Coprime-cofactor membership criterion, native loading checks, native trace statistical completeness on subgroups |
| [Instances/Subgroup17.lean](EfficientFFA/Instances/Subgroup17.lean) and [Tests/Subgroup.lean](Tests/Subgroup.lean) | A 22-point curve, an order-11 subgroup, 8/11 native bound, ambient two-torsion rejection and a counterexample without coprime cofactor |
| [Shared complete-add constraints](EfficientFFA/Native/CompleteCircuit.lean) | Native selector soundness, shared limb copies, equivalence to ordered complete addition and witness existence |
| [Native regressions](Tests/Native.lean) | Square linkage, wrong outputs, active/inactive branches, native wraparound, explicit quotient witnesses and all new theorem-axiom reports |
| [Trace regressions](Tests/Trace.lean) | Accepted concrete curve traces, wrong output, broken initial linkage, and a nonempty execution returning infinity |
| [MSM regressions](Tests/MSM.lean) | Unequal windows, accepted execution, exact excluded-seed counts, instantiated probability theorem, and noninvertible coefficient |
| [Table regressions](Tests/Tables.lean) and [parameter regressions](Tests/Parameters.lean) | Accepted concrete table, known rejected offsets, prime/composite group parameters, and failure without scalar invertibility |
| [EC regressions](Tests/EllipticCurve.lean) | Concrete order-two/order-three points, missing-precondition counterexample, and distinct infinity encodings |
| [Foundations.lean](Tests/Foundations.lean) | Noncoprime/signed/zero moduli, strict-bound boundary, a radix-10 multiplication example, signed limbs, and theorem-axiom reports |

## Source policy

Use the paper as the mathematical specification and Lean/mathlib as the proof
foundation. Do not consult or copy the supplied external Lean repository or
ZIP. No proof sources from that artifact were used. The dependency checkout
originated in a pristine standard-library cache.

The initial paper source was 2025-695.pdf, SHA-256
c075bb9c3db566eb579495e64eb074c2783cdba34dcd1417132eb5756e7b36dd.
Current correspondence uses the paper revision linked above. Field constants
were cross-checked against arkworks; exact references are recorded in
[Constants.lean](EfficientFFA/Instances/PaperParameters/Constants.lean).

The EasyCrypt coverage inventory may inform priorities; its scripts are not
proof-translation templates. At the user's request on 2026-10-27, the table
and rejection results were compared with EasyCrypt, informing subsequent
parameter selection. Independence means fresh definitions and proofs, not
absence of prior artifact reviews. The supplied external Lean artifact remains
unconsulted.

Keep assumptions and representation boundaries explicit. Do not introduce
admissions, project axioms or silent statement weakenings. Maintain the results
map when contracts change, and run lake build after proof changes. Mathematical
counterexample regressions remain part of the default checks.

See [AGENTS.md](AGENTS.md), the [repository overview](../README.md) and
[shared coverage guide](../docs/coverage.md). The paper is maintained separately
in miguel-ambrona/ffa-paper; edit it only when requested.
