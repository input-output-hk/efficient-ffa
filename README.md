# Efficient Foreign-Field Arithmetic in PLONK
Formalization of proofs for efficient foreign field arithmetic (FFA) and multi-scalar multiplication (MSM) algorithms developed at IOG/Midnight.

See more in the associated [paper](https://eprint.iacr.org/2025/695).

## Current status

The agreed formalization work is complete through small concrete MSM and
FFA instances. The generic theorems retain explicit assumptions; the small
instances discharge their project algebra, representation, sampler and
parameter obligations. The LCM properties are proved from integer arithmetic.

- [SmallCurve.ec](SmallCurve.ec) and [SmallMSM.ec](SmallMSM.ec) instantiate
  the full coordinate-witness proofs on a seven-point curve over F_5,
  with w=T=l=1 and a checked rejection upper bound of 6/7.
- [SmallFFA.ec](SmallFFA.ec) instantiates multiplication soundness and
  completeness with two 2-bit limbs, q=13, p=127 and auxiliary modulus 2.
- The last full strict check passed for 32 root theories and 26 regression
  files, including every expected proof failure. The supplied EasyCrypt
  standard library remains trusted.

Automated provisioning/CI and larger or production instances are skipped
for the current scope. Paper synchronization is deferred. Circuit wiring,
gate counts and comparison with a production implementation are outside
scope. See [the repair status record](FORMALIZATION_REPAIR_PLAN.md) for the
completed work and precise validation limits.

## Toolchain and checks

The validated versions are recorded in [toolchain.json](toolchain.json).
Install those tools, register Alt-Ergo and Z3 with Why3, then run:

```bash
EASYCRYPT=/path/to/easycrypt ./scripts/check-local.sh -why3 /path/to/why3.conf
```

The script checks every retained local theory independently, including
all FFA dependencies, then the positive and negative regression files.
It rejects explicit admissions and weak/report proof modes, accounting for
nested comments. Standard-library proofs are trusted as supplied rather
than rechecked. Python 3 and Bash are needed for the check scripts.

The toolchain manifest records tested versions; automated environment
provisioning and CI integration are skipped for this scope. The original
upstream requirements were EasyCrypt a214a56, Jasmin 2023.06.1, Alt-Ergo >= 2.5.1,
CVC4 >= 1.8 and Z3 >= 4.8.7. The current scripts target the newer recorded
EasyCrypt revision.

## Contents

* `FFA_soundness.ec` the proof that whenever the system of constraints is satisfied then we have correctly multiplied foreign field elements.
* `FFA_completeness.ec` the converse of the above.
* `FFA.ec` some common definitions.
* `MultiScalarMul_Abstract_Setup.ec` abstract setup for MSM algorithms.
* `MultiScalarMul_Abstract.ec` correctness of unoptimized (perfect) MSM algorithm.
* `MultiScalarMul_Abstract_Completeness.ec` statistical completeness of optimized MSM.
* `MultiScalarMul_Abstract_Soundness.ec` perfect soundness of optimized MSM.
* `MSM_FullCoordinates.ec` full coordinate-witness soundness and completeness.
* `MSM_WindowOrder.ec` verified little-endian interfaces to the big-endian core.
* `SmallCurve.ec`, `SmallMSM.ec` and `SmallFFA.ec` concrete instances.
* `IntegerLCM.ec` concrete LCM construction and divisibility proofs.
* `MSM_Instance.ec` and `FFA_Instance.ec` generated packages for specialization.


## Local MSM axiom repair

This checkout contains a repair against upstream commit
`08504b2d13f40bd219be13e8b3522e14bae595b4`.

Two independent contradictions were found:

- `no_order_two_elems` applied to `idR` asserted that doubling the identity
  is nonidentity, contradicting `mul_idr`. It now requires `x <> idR`.
- The admitted `iteri_ub3` theorem allowed negative iteration counts.
  At `N = -1`, `p = 1`, its per-iteration condition is vacuous and its
  conclusion bounds a nonnegative probability by `-1`. It now requires
  `0 <= N`, and both formerly admitted steps are proved.

The abstract `u_check` operation and its all-integer table axiom have been
replaced by a definition. Acceptance requires a nonzero initial accumulator
`l *** U`, valid window values, and nonidentity table entries at the
bounded indices actually read. This changes the admissibility condition;
it is not merely a change to a proof script.

The loop equivalence proof now maintains nonidentity of the accumulator
on accepted executions and proves the new doubling premise at each
iteration. The two admitted group-iteration lemmas and the admitted
divisibility lemma also have proofs. The full local proof-policy check finds
no active admissions or weak/report proof modes. The core scalar-window comment says **big-endian**, matching
its specification and forward loop. The little-endian interface below
provides a verified index reversal for the paper and Lean convention.

### Historical MSM repair checks

The MSM repair was checked with:

```text
EasyCrypt a2cd7bf1e18d2b0c299f2b13d6004343dd1bf1ca
Why3      1.8.2
Alt-Ergo  2.6.3
Z3        4.8.12
OCaml     5.2.1
```

This is newer than the original requirements above. Compatibility changes
remove obsolete `nosmt` annotations, update probability-one proof
composition and a memory binder, fix a stale unfolding name, and make
several arithmetic/group proof steps explicit.

Run:

```bash
EASYCRYPT=/path/to/easycrypt ./scripts/check-msm.sh -why3 /path/to/why3.conf
```

Omit `-why3` when the default configuration already registers both solvers.
This narrower script checks the six theories in the original MSM repair
and tests/MSM_Regression.ec. It also requires tests/LegacyAxiomMustFail.ec
and tests/NegativeIterationsMustFail.ec to be rejected. It does not cover
the later coordinate proofs or concrete instances; use scripts/check-local.sh
above for the complete current artifact.
In temporary copies restoring the corresponding original declaration,
each negative test successfully proved `false`; both fail after repair.
These tests detect the two known contradictions, not arbitrary
inconsistency.

A separate `-check-all` attempt, which also rechecks EasyCrypt's standard
library, failed in that library's `List.ec` at line 2687 before reaching
the project. The local check script therefore uses the standard library
as supplied. The checker warns about the OCaml 5.2.1 garbage collector.

## Audit cleanup

Unused `WhileApprox.eca`, `JWord_array.ec` and the processor-specific portion
of `JWord.ec` have been removed. The generic word theory and limb arithmetic
needed by FFA remain. This removes an unsound admitted loop bound and an
incorrect SIMD comparison from code outside the FFA/MSM dependency paths.

See [the repair status record](FORMALIZATION_REPAIR_PLAN.md) for the completed
sampler, table-construction, rejection-bound and concrete-instance work.

## Sampler normalization repair

The abstract random-point distribution now explicitly assumes
`is_lossless r_distr`. Full support and uniform point masses alone do not
imply normalization. `tests/DistributionSemantics.ec` proves that a half-mass
singleton distribution is full and uniform but not lossless;
`tests/NonLosslessSamplerMustFail.ec` must fail to prove its sampler lossless.

The completeness theory proves `UniformU_lossless`, instantiates soundness
as `MSM_uniform_soundness`, and proves termination of the corresponding MSM
run as `MSM_uniform_lossless`. The new `MSM_uniform_success` theorem gives:

```text
Pr[MultiScalarMul(UniformU).run(P,s) returns an accepted result]
  >= 1 - (p2 P s + 2*T*l*p1).
```

This theorem concerns the original ideal-table program and retains the
symbolic p2 term. MSM_RejectionBound.ec supplies the explicit bound for
the constructed-table program, and MSM_FullCoordinates.ec transfers it to
full coordinate-witness existence. SmallCurve.ec discharges normalization
with a concrete finite uniform sampler; SmallMSM.ec specializes the bound
to 6/7. These results concern the mathematical model.

## Guarded table construction and composition

`MSM_TableConstruction.ec` now defines an imperative builder for all
`2^w` entries of each row. It rejects zero base points, a zero initial
entry, and any step whose operands are zero or have equal x-coordinates.
It executes an incomplete addition only after checking these conditions.
A failed row makes the whole table unsuccessful.

The checked specifications establish termination, exact acceptance according
to `row_safe`/`table_safe`, and agreement of every accepted entry with
`perfect_table_pure`. For nonzero P and positive row width b,
`row_admissible_safe` proves the sufficient condition:

```text
V != j*P for every -1 <= j <= b-1.
```

`MSM_WithTable.ec` defines `ConstructedMSM.run`, which builds the table,
rejects construction failures and invalid windows, then runs the optimized
MSM using the returned entries. Its execution path does not read the ideal
table or call the ideal-table admissibility check. The initialization check
reduces to `l*U != identity` because table safety and valid windows establish
the other admissibility conditions.

`constructed_msm_soundness` and `sampled_constructed_msm_soundness` prove
probability-one termination and correctness of accepted results for this
composed path. Regressions prove that V = 2P and zero base points are
rejected, and admissible rows are constructed correctly. The claim
that x(P) != x(V) alone guarantees successful construction is an
expected-failure regression.

This program uses the abstract group interface for offsets, doubling and
final correction. The full coordinate-witness proofs below supply the
operation traces, and SmallCurve.ec realizes the representation model.
The guarded builder models safe witness construction. As proved below,
accepting table constraints already imply its per-step guards, so these
guards need not become additional circuit assertions. The rejection bound
below covers `SampledConstructedMSM`, including
table construction. Circuit instantiation is outside the current scope.

## Rejection probability of the constructed algorithm

`MSM_RejectionBound.ec` proves the bound for the actual sampled execution:

```text
Pr[SampledConstructedMSM.run(P,s) rejects]
  <= (1 + l*(2^w+1) + 2*T*l) / q.
```

Here q is `group_cardinality`, the size of a proved finite, duplicate-free
enumeration of the entire group R. Its positivity and `p1 = 1/q` follow
from the existing full, uniform, lossless distribution assumptions; no new
cardinality axiom is introduced. This q is not silently identified with
the separate abstract `order` parameter used by the inversion axiom.

The explicit input hypotheses are nonzero base points in every used row,
valid scalar windows, and invertibility of multiplication by l and 2^w-1.
`scalar_invertible_small` discharges invertibility when the scalar's absolute
value is positive and below `order`. The result also depends on the existing
group/coordinate assumptions, positive parameters and
`completeness_constraints` used to prove the main-loop bound.

The proof combines three bounds without assuming independence:

| Failure event | Upper bound |
| --- | --- |
| Initial accumulator is the identity | 1/q |
| Guarded table construction rejects | l*(2^w+1)/q |
| MSM loop encounters a coordinate collision | 2*T*l/q |

`sampled_rejection_bound_cardinality` states the final upper bound;
`sampled_success_bound_cardinality` proves acceptance probability at least
one minus that bound. `construction_event_equiv` connects the counted event
to the program, and `sampled_constructed_lossless` accounts for termination.
The existing ideal-table completeness theorem is preserved; its loop proof
is now shared through `MSM_loop_failure_bound`.

Regressions establish that zero base points and invalid windows reject with
probability one, explaining why those inputs are excluded. They also show
that multiplication by zero has a probability-one identity event and
cannot be invertible on a nontrivial group. A claim that zero is
invertible must be rejected by the checker.

The generic bound retains explicit assumptions and is useful when
1 + l*(2^w+1) + 2*T*l is small relative to q. SmallMSM.ec specializes the
full-coordinate version to 6/7. Its regressions also compute exact rejection
masses of 3/7 and 4/7 for the two scalar values at the chosen base.

## Table constraints imply the per-step guards

`MSM_TableConstraints.ec` models Figure 2's three modular coordinate
equations and nonidentity output, without an explicit unequal-x guard in
an addition step. An accepted row includes the paper's single initial
check x(P) != x(V), nonidentity P and V, the initial entry -V, and the
addition equations at each successive entry. Every step adds the same P.

The two slope equations prevent any step from outputting P: that would
imply 2*y(P)=0. The first slope equation also rejects input -P. Together
with the initial check and the coordinate-collision property, these facts
prove that every accepting row satisfies all incomplete-addition guards.
This argument is specific to a repeated-base table; it does not remove
Figure 4's guards for the main MSM loop, whose addends vary.

- `constraints_output_not_base` and `constraints_inverse_impossible`
  prove the modular contradictions.
- `accepted_step_safe` and `accepted_step_distinct_x` prove the implied
  abstract and modular coordinate guards.
- `accepted_table_row_safe` and `accepted_table_entries` establish row
  safety and agreement with the mathematical table.
- `accepted_table_builder_succeeds` shows that the guarded builder accepts
  and reproduces any accepted witnessed row.
- `constraint_table_msm_soundness` connects witnessed tables directly to
  MSM soundness, without executing the guarded builder.

No new global axioms or admissions are added. The theorems explicitly
require `coordinate_laws` (nonzero 2*y for nonidentity points, coordinate
negation and agreement with the abstract x-coordinate comparison) and,
for result correctness, `safe_constraint_correct`: correctness of the
coordinate equations when addition inputs are safe. The coordinate-witness
extension below now derives that property from a more explicit affine
representation model, realized by SmallCurve.ec. Witnessed points in this
group-level connection are represented by the abstract type R; the later
full-coordinate relation uses raw coordinate tuples.

This corrects the earlier implication that extra per-step circuit checks
were required. V=2P still refutes the claim that the initial check alone
guarantees successful construction, but the existing equations reject
that exceptional choice. The paper should distinguish soundness of
accepting constraints from statistical completeness under random offsets.
The original rejection bound above concerns the guarded sampled program.
The coordinate-witness extension below now supplies the reverse connection
for tables and transfers that part of completeness to actual witness
existence. The full-coordinate extension below now supplies the remaining
operation traces and transfers the complete rejection bound.

Regressions check that the V=2P row has no accepting witnesses under the
interface hypotheses, and that isolated addition equations can accept
equal inputs. The latter explains why the table-chain argument and its
initial check matter.

## Scalar window order

The paper defines little-endian windows: input index i has weight 2^(w*i)
with zero-based indices. Its published forward loop instead processes the
least significant window first, which is incorrect for a doubling-first
Horner recurrence. The Lean artifact already processes higher windows first.

The corrected paper traversal is i=T,T-1,...,1 (one-based). The local
extracted LaTeX copy has this correction, the corresponding accumulator
invariant, and clarified prose/caption. `paper/endianness.patch` records
those edits relative to that copy's original `paper/source.tex`; apply it
from an unmodified extracted Lean-project root, not this repository.
The downloaded PDF has not been rebuilt or replaced. The extracted source
contains unrelated transcription artifacts and is not asserted to be the
original publication source.

`MSM_WindowOrder.ec` preserves the existing big-endian core and exposes
little-endian entry points:

- `LittleEndianMSM.run` for a fixed offset and constructed table;
- `SampledLittleEndianMSM.run` for a uniform random offset;
- `LittleEndianMSM.with_table` for supplied table entries, including the
  equation-level table soundness connection.

Each passes the index view `reverse_windows T s j i = s j (T-1-i)` to the
core. Thus processing starts at input T-1 and finishes at input 0, exactly
as in the corrected paper loop. This does not reverse bytes or bits within
a window and does not add group operations or circuit assertions.

`reversed_core_spec` proves agreement with the independent little-endian
specification `msm_little_endian`, whose window i has weight 2^(w*i).
Soundness, the supplied-table constraint theorem, and the same rejection
upper bound and success lower bound are proved for the new entry points.
The original big-endian entry points and their theorems remain available;
callers must use the entry point matching their input convention.

`tests/WindowOrder.ec` checks the actual group specifications: width 2
and windows [1,2] give 6P without reversal and 9P with reversal. It also
proves these differ for nonzero P under the existing inversion hypothesis
with order>3, so the regression cannot be hidden by small-order equality.

No Halo2/Rust implementation is present in this workspace. Comparison of
its window extraction and traversal with this interface is outside the
current scope; these proof and paper edits make no claim to change that
implementation.

## Affine addition and coordinate-table completeness

`AffineAddition.ec` is independent of the abstract group assumptions. With
an explicit prime modulus and nonzero x-coordinate difference, it proves:

- the modular inverse yields a slope satisfying the input slope equation;
- the affine formulas produce witnesses for all three addition equations;
- the equations uniquely determine slope and output coordinates modulo m;
- on-curve inputs give on-curve outputs, without assuming output membership;
- witnesses can be chosen in the canonical ranges 0 <= x,y,lambda < m.

`MSM_CoordinateWitnesses.ec` connects this arithmetic to the group/table
proofs. Its `affine_group_model` is an explicit representation obligation:
nonidentity points have injective coordinate pairs modulo m, and safe group
addition has the standard affine coordinates. SmallCurve.ec now instantiates this model for a seven-point curve, as
described below. It does not assume constraint soundness
or witness existence. Under this model and the existing coordinate laws:

- `safe_constraint_correct_from_model` derives the earlier correctness
  hypothesis from the proved coordinate uniqueness result;
- `safe_constraint_witness` constructs the slope for safe group additions;
- `safe_row_has_witnesses` and `safe_table_has_witnesses` construct table
  witnesses, with slopes in [0,m), without additional per-step guards;
- `table_constraints_iff_safe` proves equivalence of abstract table safety
  and existence of satisfying coordinate-table witnesses;
- `table_witness_failure_bound` bounds the probability that such table
  witnesses do not exist by l*(2^w+1)/group_cardinality;
- `little_endian_table_witness_failure_bound` transfers the full previously
  proved bound to the event combining coordinate-table witness existence
  with the existing abstract initialization and loop acceptance conditions;
- `modeled_little_endian_table_soundness` reuses the same representation
  model instead of assuming the coordinate constraint correctness theorem.

The row equivalence requires width >=2; the actual width 2^w satisfies this
because w>0. A regression shows why a one-entry row is a genuine boundary.
Other regressions check a concrete addition over F_17, nonuniqueness over a
composite modulus, equal-input degeneracy, and inverse-pair rejection.

No new global axioms or admissions are introduced. This completes the
coordinate-addition arithmetic and table-witness connection at the explicit
representation-model boundary. The following sections supply doubling,
complete addition, and composition through offset computations, the loop
and final correction. SmallCurve.ec discharges the representation model
for the small instance. Larger instances are skipped for the current scope;
paper synchronization is deferred.

## Doubling and complete coordinate addition

`AffineDoubling.ec` proves bounded tangent-slope witnesses, uniqueness of
slope/output modulo a prime, and curve closure. Existence and uniqueness
require a nonzero denominator 2*y; curve closure follows from the tangent
equations without that extra premise.

`AffineComplete.ec` represents a point by an explicit infinity flag and
two integer coordinates. Its complete constraint relation handles either
identity input, unequal-x addition, inverse pairs, and equal-point doubling.
It requires canonical output coordinates and encodes infinity as (true,0,0).
For prime moduli and on-curve inputs, the file proves witness existence,
unique output equal to the case-split affine formula, and output curve
membership. In particular, a zero-y point doubles to infinity. These are
arithmetic results independent of the abstract group axioms, not a proof
that a nonsingular curve forms a group. The relation is a mathematical
case split, not a claimed PLONK encoding or a constraint-count result.

`MSM_CompleteCoordinates.ec` connects these raw coordinate tuples to the
existing abstract group. Its explicit `complete_affine_model` extends the
safe-addition representation model with canonical on-curve coordinates
and the tangent formula for group doubling. Under that model and the
existing coordinate laws, `complete_add_group` proves agreement with
group addition. `complete_group_witness` gives bounded witnesses and
`complete_group_sound` identifies any accepted raw output tuple with the
encoded group sum, without assuming the output already represents a group
element. The representation obligations are discharged for the small instance below.

Regressions exercise F_17 doubling and addition, both identity branches,
inverse-pair cancellation, zero-y doubling, noncanonical representatives,
and invalid equal-x inputs. Expected failures ensure that tangent
uniqueness cannot omit its nonzero-denominator premise and that complete
witness existence cannot omit on-curve input premises.

These primitives are now composed through the full MSM trace as described
below. No new global axioms or admissions were added. Paper work remains
deferred.

## Full MSM coordinate witnesses

`MSM_CoordinateTrace.ec` defines finite traces whose intermediate values
are raw coordinate tuples. Each edge provides an existential bounded slope
witness. It proves correspondence for complete-addition chains, repeated
doubling, guarded inner-loop additions and the complete window loop.

`MSM_CoordinateTables.ec` lifts the table proof to raw coordinate rows.
Only the initial unequal-x check is present in each row: accepting later
row equations imply the remaining safety conditions. Induction proves that
every entry equals the encoded mathematical table value, without assuming
that the supplied entry already represents a group element.

`MSM_FullCoordinates.ec` composes these relations into
`full_msm_constraints`. Its existential intermediates include:

- a complete-addition chain computing l*U;
- w doublings and a subtraction computing (2^w-1)*U;
- all table entries and their incomplete-addition witnesses;
- all window doublings and guarded table additions;
- complete final subtraction of l*U, including an identity output.

Under the explicit `coordinate_laws` and `complete_affine_model` premises,
`full_msm_constraints_iff` proves that an output is accepted exactly when
`construction_accepts` holds and the output is the encoded mathematical
MSM result. `full_witness_iff` gives the corresponding existence equivalence.
The little-endian entry point uses the already verified window reversal.

`little_endian_full_failure_bound` now bounds failure to obtain the entire
coordinate witness by (1+l*(2^w+1)+2*T*l)/group_cardinality, under the same
nonzero-base, valid-window and scalar-invertibility premises as the abstract
bound. `little_endian_full_rejection_mass` proves equality with rejection
probability of `SampledLittleEndianMSM.run`. Thus completeness no longer
stops at coordinate tables combined with abstract loop acceptance.

This is a mathematical constraint relation. Complete-operation branch
selection is explicit logical case splitting; lookup indexing is a function
application; l*U uses a repeated-addition witness schedule. These choices
do not instantiate PLONK gates, prove a circuit cost, or assert a particular
implementation of public-scalar multiplication. The small instance below
discharges subgroup, coordinate, sampler and MSM parameter obligations.
The supplied standard library remains trusted.

`tests/FullCoordinates.ec` constructs complete F_17 witness traces at
w=T=l=1 for scalars one and zero, checks rejection of a width-three V=2P
row, and shows why final correction cannot be omitted. The zero-scalar
trace ends at infinity. The full local check includes these regressions
and the concrete instances below, with no admissions or weak proof modes.

## Small concrete MSM instance

SmallCurve.ec instantiates the entire MSM proof chain on the nonsingular
curve y^2=x^3+2x+1 over F_5. Its generator G=(0,1) has order seven:

| n | nG |
|---|---|
| 0 | infinity |
| 1 | (0,1) |
| 2 | (1,3) |
| 3 | (3,3) |
| 4 | (3,2) |
| 5 | (1,2) |
| 6 | (0,4) |

Points are represented internally by their discrete logarithms in Z/7Z.
The additive group and scalar laws come from EasyCrypt's prime-field
library. Exhaustive checked cases verify that the coordinate table agrees
with affine addition, tangent doubling, negation and coordinate
injectivity. Thus the table supplies a concrete curve representation;
coordinate correctness is proved. The optimized abstract operation is
totalized as group addition; its safe-input behavior is connected to the
raw affine constraints by the verified model.

All project axioms of the cloned MSM theory are discharged, including
nonzero repeated doubling, scalar inversion, the full/uniform/lossless
sampler and completeness parameter inequalities. Sampling uses the
library's uniform distribution on the seven residues. The parameters are
w=T=l=1. This is a small mathematical instance, not a cryptographic curve
or a circuit implementation. The supplied standard library remains trusted.

SmallMSM.ec applies the existing full-coordinate theorems without any
remaining representation premises. It proves accepted-output correctness,
a failure-probability bound of 6/7 for every nonzero base and valid scalar
window, and equality between missing-witness mass and sampled-program
rejection probability.

tests/SmallCurveInstance.ec verifies full witnesses for scalar zero
(result infinity) and scalar one (result G), using U=2G. It rejects a wrong
output, enumerates exact rejection masses 3/7 and 4/7, and proves the
sampled little-endian program's rejection probability is 4/7 for scalar
one. A negative regression must fail to prove the wrong output acceptable.

The original files use external imports, which cannot be specialized by
cloning a downstream theorem alone. MSM_Instance.ec therefore packages
the existing sources as nested theories inside an abstract model. It is generated mechanically:

~~~sh
python3 scripts/package-msm.py
~~~

The generator preserves all declarations and proof bodies, adjusting imports
and two explicit root-qualified references. The auxiliary theory now includes
the concrete LCM definition and its proved lemmas; no exclusion is needed. The local
check rejects a stale generated file and checks its proofs independently,
then checks the concrete clone and every discharged obligation. Edit the
original sources and regenerate the package rather than editing it by hand.

## Concrete integer LCM

IntegerLCM.ec replaces the former abstract LCM operation with a fold
of the binary definition abs(a * (b / gcd(a,b))), using integer division.
Bézout's identity and the standard library's proved gcd laws establish
that this binary result divides x exactly when both inputs divide x.
Induction lifts the property to the indexed family 0 <= i < n.

The file proves nonnegativity, the common-multiple and least-positive
properties, and the corresponding equivalence for arbitrary equal residues.
It handles signed and zero moduli without coprimality assumptions:

- empty families, including negative lengths, have LCM 1;
- a singleton has LCM abs(M(0));
- an included zero modulus gives LCM 0, and this is the only way LCM is zero;
- families of nonzero moduli have positive LCM.

AuxResults.ec retains the names LCM, LCM_pos and
chinese_reminder_theorem for existing callers. Both former axioms are now
proved lemmas with unchanged statements. The historical Chinese-remainder
name denotes the LCM divisibility equivalence; it does not assert existence
of a solution for arbitrary prescribed residues.

tests/LCMRegression.ec checks empty, negative-length, signed, repeated,
zero and noncoprime inputs. It also proves LCM(4,6,5)=60 and reconstructs
equal integers in [0,60) from equal residues modulo 4, 6 and 5. Negative
regressions reject replacing LCM(4,6) with 24 and asserting strict positivity
when a modulus is zero. These examples exercise the LCM layer; the small
FFA instance below also uses it to discharge both combined-modulus inequalities.

## Small concrete FFA instance

SmallFFA.ec instantiates both original multiplication proofs with the following
parameters. Word values are pairs of booleans, and two-limb arrays are pairs
of words; all cloned representation obligations and definition equations are
proved. Both field moduli are proved prime.

| Parameter | Value |
|---|---|
| Word width / radix | 2 bits / B=4 |
| Number of limbs / represented integers | 2 / 0 through 15 |
| Foreign modulus q / native modulus p | 13 / 127 |
| Auxiliary moduli | one modulus, 2 |
| Witness widths t1 / t2 | 4 / 5 |
| K_min / K_max | -1 / 8 |
| L_min / L_max | -10 / 8 |
| Auxiliary lower / upper bounds | -64 / 37 |
| LCM(2,127) | 254 |

The witness bounds are 0 <= u < 16 and 0 <= v < 32. The auxiliary interval
lies strictly inside (-127,127); the two global reconstruction bounds are
210 < 254 and 121 < 254. All inequalities are discharged inside EasyCrypt.

The acceptance predicate consists of these witness ranges and the existing
native and auxiliary equations modulo 127. concrete_sound and
concrete_complete apply the original proofs; concrete_iff combines them:

~~~text
(exists bounded u,v satisfying the constraints)
  iff bn(x)*bn(y) mod 13 = bn(z) mod 13.
~~~

Every residue modulo 13 has a concrete limb encoding. The theorem covers
all represented integers, including 13, 14 and 15, which are noncanonical
foreign-field representatives. canonical_output adds bn(z)<13 to obtain
integer equality with the canonical modular product. No canonical-input
premise is needed for soundness.

tests/SmallFFARegression.ec checks 7*8=4 modulo 13, zero, maximal limbs,
noncanonical inputs and outputs, completeness for every residue pair, and
the little-endian limb convention. It also proves that the wrong equation
1*3=0 passes the native congruence with u=11: its left-hand side is -127.
Adding v=69 makes the auxiliary left-hand side -127 too, but violates its
range bound. With both bounds enforced, every witness for that wrong product
is rejected. An expected-failure regression must fail to prove it acceptable.

FFA_Instance.ec mechanically packages FFA.ec, FFA_soundness.ec and
FFA_completeness.ec as nested theories so their shared parameters can be
specialized together. The generator preserves all declarations and proof
bodies, adjusting imports only:

~~~sh
python3 scripts/package-ffa.py
~~~

The full local checker rejects stale generated sources and checks the package,
the concrete instance and its regressions independently. Edit the original
proofs and regenerate the package rather than editing it by hand.

This is a small mathematical instance, with q<p. It demonstrates consistency
of the project assumptions and exercises the original FFA proof chain; it is
not a production parameter selection, a large-foreign-modulus example, or a
circuit implementation. The supplied EasyCrypt standard library remains trusted.
