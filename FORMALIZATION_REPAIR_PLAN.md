# Repair plan for the FFA and MSM formalization

Status: 2026-10-21, following the axiom repair in commit c0ed96d.
Cleanup, a full local proof check and the abstract sampler-normalization
repair are implemented. Guarded table construction and its composition
with MSM are now checked at the abstract group level. Environment
provisioning/CI and concrete instantiations remain open. The constructed
algorithm now has a checked symbolic rejection bound. Circuit instantiation
is outside the requested scope.
An equation-level table proof now shows that accepting witnesses imply
the per-step guards, using only the paper's initial unequal-x check.
The original paper PDF and Lean proofs have not been changed. The local
extracted LaTeX copy now has the endianness correction described below.

## Cleanup completed

- Removed unused WhileApprox.eca, including its unsound admitted loop bound.
- Reduced JWord.ec to the generic BitWord theory used by JBigNum. Removed
  unused processor flags, ALU, fixed-width words, SIMD and instruction models,
  including the incorrect signed comparison implementation.
- Removed unused JWord_array.ec and its import, a commented-out admitted
  iteration lemma, stale Jasmin import comments and two debug print commands.
- Retained the limb arithmetic, abstract MSM assumptions and contradiction
  regression tests: these support the actual proofs and must be addressed
  explicitly rather than deleted to make the audit look clean.

The historical audit runner in ../formalization-audit/run_audit.py now reads
its inputs from c0ed96d by default, so probes for deleted code remain
reproducible without bringing that code back into the live formalization.

## 1. Establish a reproducible full local build

The tested toolchain is recorded in toolchain.json. Compatibility repairs
are now in the checkout: obsolete nosmt annotations are removed, FFA
sum-bound proof binders are updated, and nonlinear arithmetic steps are
made explicit. In particular, lex_lt uses multiplication monotonicity;
lex_le and lex_eq follow from the comparison lemmas. No theorem statements
were weakened and no axioms were added to repair these proof failures.

scripts/check-local.sh checks every retained local theory as a top-level
file, plus all positive regressions and expected failures. This closes the
previous JBigNum failure and the isolated-copy limitation. The proof-policy
guard rejects explicit admissions and weak/report modes while ignoring
nested comments. A prior full standard-library recheck stopped in
EasyCrypt's List.ec; the script trusts the supplied standard library.

Still open: provide automated environment provisioning and integrate the
command into CI. toolchain.json records tested versions but is not a
transitive dependency lock or an installer. The tested OCaml 5.2.1 emits
a GC-regression warning; a move to a newer OCaml needs its own validation.

Acceptance: the local command now checks the complete project proof chain.
The remaining build work is a pinned, provisioned CI environment running
that same command, including the admission guard and negative regressions.

## 2. Normalize the random sampler and connect the theorems

In EasyCrypt a214a56, theories/distributions/Distr.ec defines:

- is_full d: every value belongs to the support of d.
- is_uniform d: any two support values have equal point mass.
- is_lossless d: weight d = 1.

The first two predicates do not imply the third. A distribution assigning
mass 1/2 to the sole value of unit is full and uniform with weight 1/2.
../formalization-audit/PartialUniform.ec checks this example on the newer
toolchain; the predicate definitions were also inspected in the original
pinned revision. Scaling a normalized finite uniform distribution by 1/2
illustrates the same distinction on a larger finite type.

Implemented: r_distr_ll explicitly requires losslessness in the abstract
interface. UniformU_lossless proves the sampler terminates;
MSM_uniform_soundness instantiates the existing soundness theorem with it.
MSM_uniform_lossless proves termination of the sampled MSM run, and
MSM_uniform_success complements the existing failure bound to give a
success lower bound for that same program and inputs.

Regression coverage now includes tests/DistributionSemantics.ec (full,
uniform, half mass, not lossless) and tests/NonLosslessSamplerMustFail.ec
(the half-mass sampler cannot satisfy a losslessness obligation). The
complete local check includes both.

Still open in step 5: discharge r_distr_ll using a concrete finite uniform
sampler. The new abstract success bound still contains p2; it does not
establish a small failure probability or verify concrete table construction.

## 3. Verify table construction before finalizing rejection bounds

Implemented in MSM_TableConstruction.ec: a guarded imperative row builder
and a complete multirow builder. Each incomplete addition is preceded by
nonidentity and unequal-x checks. Zero base points are explicitly rejected.
The probability-one specifications prove termination, exact acceptance
according to row_safe/table_safe, and correctness of all returned table
entries on acceptance. row_admissible_safe proves the corrected sufficient
exclusion set V != jP for -1 <= j <= b-1, with P nonzero and b positive.

Implemented in MSM_WithTable.ec: ConstructedMSM.run consumes the returned
table, rejecting failed construction and invalid windows. The optimized
loop is equivalent to the original ideal-table loop when the builder
succeeds. Table safety reduces its initial admissibility check to l*U != O;
the new execution path does not consult perfect_table_pure or u_check.
Both fixed-U and sampled executions have checked probability-one soundness
statements, including termination. The legacy ideal-table entry points
remain available for the existing completeness proof.

Regressions check rejection for V = 2P and zero P, acceptance and exact row
contents under row_admissible, and expected rejection of the old weak
sufficient-condition claim. scripts/check-local.sh includes these files.

Implemented in MSM_TableConstraints.ec: the modular slope equations rule
out output P and input -P. Consequently, a repeated-base table satisfying
the existing equations and the single initial x(P) != x(V) check satisfies
row_safe; its entries match the mathematical table and can be passed
directly to the verified MSM loop. No extra per-step circuit guards are
needed for this soundness argument. The initial proof uses explicit coordinate laws and a safe-input
coordinate-addition correctness hypothesis, with no new global axioms.
The coordinate-witness extension below now derives this hypothesis from
an affine representation model and proves the reverse witness-existence
direction for row widths >=2. No concrete curve is instantiated.

The guarded builder remains a witness-construction model. Its rejection
condition is now covered by step 4. Coordinate operations and complete
operations for offsets/doubling/correction retain their stated assumptions.
Circuit instantiation is outside the requested scope.

## 4. Prove a useful completeness bound

Implemented in MSM_RejectionBound.ec:

- A finite-interval union bound with no independence premise.
- Exact point-event mass under invertible scalar multiplication.
- Guarded table rejection at most l*(2^w+1)*p1 for nonzero base points.
- Initialization rejection at most p1.
- A shared main-loop bound 2*T*l*p1, extracted from the existing completeness
  proof as MSM_loop_failure_bound without changing its assumptions.
- A probability-one flag specification and construction_event_equiv linking
  the mathematical acceptance event to SampledConstructedMSM.run.
- The actual program rejection bound (1+l*(2^w+1)+2*T*l)*p1 and its success
  lower bound, under valid windows and explicit invertibility hypotheses.
- A finite, unique enumeration covering all of R, positive group cardinality
  q, and p1=1/q derived from the existing distribution assumptions. Thus the
  final bound is (1+l*(2^w+1)+2*T*l)/q, with no unresolved p2 term.

The main-loop parameter assumptions remain completeness_constraints; the
new scalar-invertibility premises can be discharged using invertmeP when
0 < abs(n) < order. The cardinality q is not assumed equal to that separate
order parameter. The theorem is conditional on the existing algebraic and
coordinate axioms and on the full, uniform, normalized sampler.

Regressions show why nonzero bases, valid windows and invertibility matter:
zero bases and invalid encodings reject with probability one, and the zero
scalar is not invertible on a nontrivial group. No new axioms or admissions
were added for this bound.

Remaining optional specialization: choose concrete parameters, establish
the stated inequalities and invertibility conditions, and evaluate the
bound numerically. The symbolic abstract rejection-bound task is complete;
this does not require circuit instantiation.

## 5. Discharge the concrete algebra and arithmetic assumptions

Build a concrete elliptic-curve subgroup instance. Derive same_res and
opt_never_id from the actual incomplete coordinate formulas; prove the
coordinate-collision, scalar-inversion and nonzero-doubling properties.
Handle the identity explicitly in the coordinate representation, since the
current notxdiff axiom quantifies over it too. Establish on-curve and subgroup
membership of inputs and outputs. A small abstract group example is useful
for testing but does not establish this curve instance.

For FFA, replace the abstract LCM/Chinese remainder assumptions with a
concrete finite least-common-multiple construction and proved divisibility
properties, or instantiate them from a checked arithmetic library. Instantiate
all limb widths, field moduli, auxiliary moduli and range/product bounds.
Show precisely which conclusions are modular equalities and which require
canonical representatives.

Circuit instantiation is outside the current scope. A concrete curve model
would be separate work to discharge the abstract interfaces, rather than a
prerequisite for the conditional MSM bound proved in step 4. Publish an
explicit list of assumptions intentionally retained.

## Paper synchronization

After each step, update the formalization-status claims and theorem
hypotheses in the paper. Describe the present artifact as conditional
abstract MSM correctness,
including the table-constraint soundness connection, plus range-bounded
FFA constraint proofs. Explain that accepting table constraints imply
the per-step guards; the initial check does not guarantee that every
choice of random offset allows successful construction. Keep the external
little-endian convention consistent with descending traversal and the
verified EasyCrypt reversal interface. Explain separately which counterexamples
exposed inconsistent assumptions, which exposed an unverified algorithm
stage, and which were merely unused library defects.

Suggested review units: build/CI; sampler normalization and instantiation;
table builder; quantitative rejection bound; optional concrete curve and FFA
parameters/CRT; final paper claims. Circuit composition is out of scope.

## Window-order correction implemented

The paper and Lean artifact use little-endian scalar windows. Preserve that
interface and process indices in descending order. The local extracted
LaTeX source now corrects Figure 4 and its surrounding prose, with the
post-window invariant acc = l*U + sum_j sum_(r=i..T) 2^(w*(r-i))*s[j,r]*P[j].
The reviewable changes are retained in paper/endianness.patch; the original
PDF is unchanged.

MSM_WindowOrder.ec implements little-endian adapters for fixed-offset,
sampled, and supplied-table execution. A group-sum reindexing proof shows
that reversing the input view gives the independent little-endian weighted
sum. All soundness connections and the rejection/success bounds transfer.
The established core still explicitly accepts big-endian windows.

The new regression checks [1,2] in base 4 against both actual specifications
and proves 6P != 9P under nontriviality/inversion premises. No new axioms
are introduced. The remaining implementation check needs the Halo2 source,
which is absent from this workspace; no production convention is inferred.

## Execution status: coordinate witnesses

Paper work is deferred at the user's request. This stage changes only the
formalization, its regressions and repository documentation.

Completed in AffineAddition.ec: prime-field slope existence, unique output
coordinates for safe addition, curve closure without an output-membership
premise, and bounded representative witnesses. These proofs use integer
modular arithmetic and library inversion results, without group axioms.

Completed in MSM_CoordinateWitnesses.ec: derive safe_constraint_correct
from coordinate injectivity and the standard affine representation of the
group law; construct row/table slopes in [0,m); prove table safety iff
coordinate-table witnesses exist; transfer the table failure bound, and
combine it with the existing abstract loop bound for little-endian inputs.
The model obligation affine_group_model is explicit and uninstantiated;
this has not silently discharged the concrete group/curve representation.

Completed in the next stage (2026-10-22): `AffineDoubling.ec` proves
bounded tangent witnesses, uniqueness under a nonzero tangent denominator,
and curve closure. `AffineComplete.ec` supplies a complete coordinate
relation with explicit infinity, identity/inverse/zero-y branches, bounded
witness existence, unique output, and closure for on-curve inputs.
`MSM_CompleteCoordinates.ec` connects this relation to abstract group
addition under explicit canonical-coordinate and tangent-formula model
obligations. These obligations remain uninstantiated; no group axioms or
output-membership assumptions were added to the raw arithmetic proofs.
The case-split relation is not a PLONK encoding or a circuit-cost claim.

Next proof stage:

1. Discharge concrete subgroup/coordinate, sampler and FFA CRT assumptions,
   and check concrete parameter instances.
2. Provision and pin the checker environment in CI.

Validation adds actual numeric and boundary regressions, including a
composite-modulus counterexample to uniqueness. No paper files are edited.

The complete-coordinate stage adds numerical/boundary regressions and two
expected proof failures for missing tangent-denominator and on-curve input
premises. The full-trace extension below brings the local check to 26 theories and
19 regression files.

## Full coordinate-trace composition completed (2026-10-22)

`MSM_CoordinateTrace.ec` proves raw-coordinate chain, doubling, inner-loop
and outer-loop correspondence. `MSM_CoordinateTables.ec` proves that raw
accepted table entries have the intended group encodings and imply table
safety. Table rows still have only the initial unequal-x check.

`MSM_FullCoordinates.ec` defines a full raw-coordinate relation, including
complete offset calculations, all table and loop witnesses, and complete
final correction. Accepted outputs coincide exactly with abstract
construction acceptance and the encoded MSM result. The little-endian
failure bound now concerns absence of these full witnesses; its event
has exactly the sampled program's rejection probability. No intermediate
output-group-membership premise or new global axiom was introduced.

The representation model remains conditional and uninstantiated. Logical
complete-operation branches and function-valued table lookups are not a
PLONK/circuit instantiation. Computing l*U by repeated complete addition
is a witness schedule, not an efficiency or gate-count claim. Paper work
remains deferred.

Regressions construct complete F_17 traces for scalar one (result P) and
zero (result infinity), and reject the exceptional V=2P width-three row
and an omitted final correction.

## Small concrete instance completed (2026-10-22)

SmallCurve.ec discharges every project axiom in a clone of the complete MSM
proof chain: a seven-element group with coordinates on y^2=x^3+2x+1 over
F_5, a full/uniform/lossless sampler, and w=T=l=1. It proves the coordinate
laws and complete affine model, including all safe-addition and doubling
cases. SmallMSM.ec applies the existing full-witness soundness, rejection
bound (6/7), and sampled-program correspondence without representation
premises. Numerical regressions establish full witnesses for zero and one,
exact rejection masses 3/7 and 4/7, and wrong-output rejection.

MSM_Instance.ec is a reproducible nested-theory package of the existing
proof sources, needed to specialize their shared abstract types. The build
checks both source freshness and the packaged proofs. All MSM axioms are
realized in the concrete clone. The later LCM repair below removes the
need to exclude FFA LCM declarations from this package.

Remaining: production-curve instances if desired, concrete FFA
parameters, and pinned CI provisioning. Paper and circuit work remain
deferred. The small instance uses the existing trusted standard library.

## LCM assumptions discharged (2026-10-22)

IntegerLCM.ec defines a binary gcd-based LCM and folds it over the indexed
moduli. It proves the full divisibility equivalence for arbitrary integers,
without adding assumptions about positive lengths, positive moduli or
pairwise coprimality. Empty/negative lengths give 1; zero moduli give 0;
signed moduli are normalized by absolute value. Leastness, positivity for
nonzero families, and equal-residue congruence are also proved.

AuxResults.ec now defines LCM concretely and proves LCM_pos and
chinese_reminder_theorem with exactly their previous statements. FFA
callers keep the existing interface. The latter name is historical: its
statement is a divisibility property, not a general CRT existence theorem.

The MSM package generator now preserves every declaration, including these
proved LCM definitions and lemmas. Its special exclusion block was removed.
Regressions check noncoprime/signed/repeated/zero and empty-family cases,
plus bounded reconstruction with moduli 4,6,5. Two negative regressions
reject the product shortcut and unjustified strict positivity.

The remaining FFA task is a concrete parameter instance satisfying the
soundness/completeness hypotheses. Pinned CI provisioning remains open;
paper work stays deferred.
