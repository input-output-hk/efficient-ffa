# Repair status for the FFA and MSM formalization

Status: 2026-10-22, following the concrete FFA instance in commit ef79cf5.
The agreed formalization work is complete through small concrete MSM and
FFA instances. This file records the completed repairs, validation limits
and current scope; detailed theorem descriptions are in [README.md](README.md).

## Current scope

| Area | Status |
|---|---|
| Axiom repairs and unused-code cleanup | Complete |
| Full strict local proof checks | Complete; 58 files validated |
| Sampler normalization | Explicit in the generic interface; realized in the small MSM instance |
| Table construction and implied table guards | Complete |
| Quantitative rejection bound and full coordinate witnesses | Complete |
| Little-endian MSM interface | Complete |
| Concrete curve, sampler and MSM parameters | Complete for the seven-point instance over F_5 |
| Integer LCM and divisibility properties | Complete |
| Concrete FFA representation and parameters | Complete for two 2-bit limbs, q=13, p=127, M(0)=2 |
| Automated provisioning and CI | Skipped for the current scope |
| Larger or production curve/FFA instances | Skipped for the current scope |
| Paper synchronization | Deferred |
| Circuit wiring, gate counts and production implementation comparison | Outside scope |

The generic interfaces retain explicit assumptions. The small instances
discharge their project algebra, representation, distribution and numerical
obligations. They establish concrete mathematical models, with the supplied
EasyCrypt standard library still trusted. They do not establish production
parameters or a correspondence with an implementation absent from this repository.

## Completed repairs

### Axioms and unused code

The repair began against upstream commit
08504b2d13f40bd219be13e8b3522e14bae595b4. The two known contradictions were
removed: no_order_two_elems now excludes the identity, and iteri_ub3 now
requires a nonnegative iteration count. The former admitted iteration and
divisibility lemmas are proved. Acceptance uses a defined, bounded u_check.

Unused WhileApprox.eca and JWord_array.ec were removed. JWord.ec retains
the generic word theory needed by FFA; unrelated processor, SIMD and
instruction models were removed. This cleanup removed an admitted loop
bound and an incorrect signed comparison outside the retained proof paths.

The historical audit runner in the sibling formalization-audit directory
uses commit c0ed96d by default so probes of deleted code remain reproducible.
That audit directory is a workspace artifact, not part of this repository.
LegacyAxiomMustFail.ec and NegativeIterationsMustFail.ec check the two known
contradictions. These regressions do not detect every possible inconsistency.

### Local checking and sampler normalization

Compatibility repairs allow every retained local theory to be checked
independently with the versions recorded in [toolchain.json](toolchain.json).
No theorem statement was weakened or axiom added to repair those build failures.
The full command is [documented in the README](README.md#toolchain-and-checks).

The abstract random-point interface explicitly requires is_lossless r_distr.
Full support and uniform point masses alone do not establish normalization:
DistributionSemantics.ec proves a full, uniform half-mass example, and
NonLosslessSamplerMustFail.ec rejects its losslessness claim.
UniformU_lossless, MSM_uniform_lossless and MSM_uniform_success connect
normalization to the original sampled program's termination and success.
SmallCurve.ec realizes the distribution obligations with the uniform
sampler on seven residues. The original p2 term is bounded in the
constructed-program results described next.

### Table construction and rejection bound

MSM_TableConstruction.ec verifies guarded construction of every table row,
including termination, exact acceptance and agreement with perfect_table_pure.
MSM_WithTable.ec composes the builder with the optimized MSM loop.
For nonzero P, V != jP for -1 <= j <= b-1 is a sufficient condition for
constructing a width-b row. The initial unequal-x check alone does not
guarantee that every offset permits successful construction.

MSM_TableConstraints.ec proves that accepting repeated-base table equations
imply all per-step incomplete-addition guards, using the paper's single
initial unequal-x check. Extra per-step table circuit guards are unnecessary
for this soundness argument. The guarded builder models witness construction.
The main loop retains its own guards because its addends vary.

MSM_RejectionBound.ec bounds actual sampled rejection by
(1+l*(2^w+1)+2*T*l)/group_cardinality. The proof combines initialization,
table-construction and loop failure events without assuming independence.
It requires nonzero bases, valid windows and the stated scalar-invertibility
and parameter hypotheses. Group cardinality is derived from the normalized
uniform distribution; it is not assumed equal to the abstract order parameter.
SmallMSM.ec specializes the full-coordinate bound to 6/7. Regressions compute
exact rejection masses of 3/7 and 4/7 for the two scalar values at the chosen base.

### Coordinate witnesses and window order

AffineAddition.ec, AffineDoubling.ec and AffineComplete.ec prove the modular
coordinate arithmetic, including witness existence, uniqueness under the
required denominator premises, curve closure and explicit identity handling.
The complete relation uses logical case splitting and canonical outputs.

MSM_CoordinateWitnesses.ec and MSM_CompleteCoordinates.ec connect this
arithmetic to explicit affine representation models. MSM_CoordinateTrace.ec,
MSM_CoordinateTables.ec and MSM_FullCoordinates.ec compose raw-coordinate
witnesses through offset calculations, table construction, all window
operations and final correction. No intermediate output-group-membership
premise is assumed. Full accepting witnesses agree with the encoded MSM
result, and their absence has the same probability as sampled-program rejection.
SmallCurve.ec realizes the coordinate laws and complete affine model.

MSM_WindowOrder.ec exposes little-endian entry points by reversing the
window index view before calling the existing big-endian core. A reindexing
proof connects the resulting computation to the independent little-endian
weighted sum. Soundness and completeness bounds transfer to these entry points.
WindowOrder.ec checks that base-4 windows [1,2] give 9P with reversal and
6P without it, and proves these differ under the stated nontriviality premises.

### Small MSM instance

SmallCurve.ec realizes every project axiom in the packaged MSM theory with
a seven-element group represented on y^2=x^3+2x+1 over F_5. Points are
represented internally by discrete logarithms in Z/7Z. Checked coordinate
cases establish the affine representation, including safe addition,
doubling and negation. Sampling is uniform on the seven residues and w=T=l=1.

SmallMSM.ec applies the full-coordinate soundness, rejection bound and
sampled-program correspondence without remaining representation premises.
SmallCurveInstance.ec checks complete witnesses for scalars zero and one,
exact rejection probabilities and rejection of a wrong output. The numerical
upper bound is 6/7; it is distinct from the exact rejection probabilities.

MSM_Instance.ec packages the existing sources as nested theories so their
shared types and parameters can be specialized together. The generator
preserves all declarations and proof bodies, adjusting imports and two
root-qualified references. No LCM declarations are excluded.

### LCM and small FFA instance

IntegerLCM.ec defines a gcd-based binary LCM and folds it over the indexed
moduli. It proves divisibility and equal-residue equivalences without
coprimality assumptions. Empty or negative lengths give 1, zero moduli give
0, and signed moduli are normalized by absolute value. Leastness and
positivity for nonzero families are also proved.

AuxResults.ec defines LCM concretely and proves LCM_pos and
chinese_reminder_theorem with their previous statements. The latter name
is historical: it denotes an LCM divisibility equivalence, not existence
of a solution for arbitrary prescribed residues. Regressions cover empty,
signed, repeated, zero and noncoprime families and bounded reconstruction.

SmallFFA.ec specializes the original multiplication soundness and
completeness proofs with B=4, two limbs, q=13, p=127, M(0)=2, t1=4 and t2=5.
Boolean pairs implement words and pairs implement limb arrays. All cloned
representation obligations and inherited definition equations are proved;
both field moduli are proved prime.

The checked values are K_min=-1, K_max=8, L_min=-10, L_max=8,
AuxLB=-64 and AuxUB=37. LCM(2,127)=254 exceeds the two required bounds
210 and 121. concrete_iff proves that bounded accepting witnesses exist
exactly when the encoded multiplication is correct modulo 13. Every foreign
residue is representable. canonical_output additionally requires an output
in [0,13) to identify it with the canonical modular product.

SmallFFARegression.ec checks explicit witnesses, zero, maximal limbs,
noncanonical representatives, all residue pairs and limb order. It also
shows that 1*3=0 passes the native congruence with u=11 and both congruences
with v=69, which violates the auxiliary witness bound. Every bounded witness
for that wrong product is rejected. An expected-failure regression prevents
it being proved acceptable in the concrete model.

FFA_Instance.ec packages the three existing FFA theories, preserving their
statements and proof bodies while adjusting imports. The small instance
has q<p; larger foreign-modulus examples and production parameters are
skipped for the current scope.

## Validation and maintenance

The last full strict check passed for 32 root theories and 26 regression
files (58 total), including 14 expected failures. scripts/check-local.sh
checks each local source independently, because ordinary imports do not
recheck its proofs. It also checks generated-source freshness and rejects
admissions and weak/report proof modes, accounting for nested comments.

After changing the original proof sources, regenerate the relevant package
with scripts/package-msm.py or scripts/package-ffa.py and run the full local
checker. Edit the original sources rather than the generated packages.
The older scripts/check-msm.sh covers only the initial repair subset.

The toolchain manifest records tested versions; it is not an installer or
a transitive dependency lock. Automated provisioning/CI is skipped for
this scope. OCaml 5.2.1 emits a GC-regression warning. A prior attempt to
recheck the supplied standard library stopped in List.ec before reaching
the project, so the local validation trusts that library.

## Deferred paper synchronization

Paper work remains deferred. The original PDF and Lean proofs have not
been changed. The local extracted LaTeX copy has an earlier window-order
correction, retained in paper/endianness.patch; the PDF has not been rebuilt.
The extracted source contains unrelated transcription artifacts and is not
asserted to be the original publication source.

When paper work resumes, align its claims and hypotheses with the current
artifact: generic conditional theorems plus the small concrete instances,
the full-coordinate rejection bound, implied table guards, and little-endian
windows processed in descending order. Distinguish contradictory assumptions,
algorithm-stage gaps and unused-library defects. The LCM result is a
proved divisibility equivalence, and the FFA output guarantee is modular
unless a canonical-output range is required.

No Halo2/Rust implementation is present in the workspace. Comparing its
window convention or circuit behavior with these mathematical interfaces
is outside the current scope. The historical release/tag remains unchanged.
