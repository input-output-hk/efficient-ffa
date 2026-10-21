# Repair plan for the FFA and MSM formalization

Status: 2026-10-21, following the axiom repair in commit c0ed96d.
Cleanup, a full local proof check and the abstract sampler-normalization
repair are implemented. Guarded table construction and its composition
with MSM are now checked at the abstract group level. Environment
provisioning/CI, quantitative bounds and concrete instantiations remain open.
The paper and Lean artifact have not been changed.

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

Still open: this is a proposed guarded algorithm in the abstract group
model. Match its checks to the actual circuit and account for their cost;
instantiate coordinate operations and the complete operations used for
initial offsets/doubling/final correction. The new rejection condition is
not yet covered by a quantitative probability bound.

## 4. Prove a useful completeness bound

The implemented valid_windows predicate requires, for all 0 <= j < l and
0 <= i < T, that 0 <= s j i < 2^w. Invalid windows currently force
rejection, so a small rejection bound cannot quantify over arbitrary s.

First bound rejection for SampledConstructedMSM, including its guarded
table builder. The old p2 term describes the original selected-entry check
and is not automatically a bound for this new program. Count forbidden U
values by proving the relevant maps injective or bijective, with explicit scalar invertibility hypotheses.
For the CURRENT selected-entry condition only, a candidate intermediate
bound is p2 <= (1 + l*T)*p1 when multiplication by l and 2^w-1 is invertible.
Combined with the existing loop bound this would give (1 + 3*l*T)*p1.
These are proof targets, not established results. For the new guarded
builder, assuming all base points are nonzero and multiplication by 2^w-1
is invertible, the proved sufficient exclusion set suggests
Pr[table rejection] <= l*(2^w+1)*p1. Establish the finite union bound and
the point-mass calculation formally. Combining that with the old bound
would first give a conservative bound; a tighter target is
(1 + l*(2^w+1) + 2*T*l)*p1 if multiplication by l is also invertible.
That tighter target requires separating main-loop failure from the old
selected-entry rejection term rather than adding p2 again. None of these
new numerical bounds is proved yet.

Relate the group cardinality to the intended subgroup order, prove
p1 = 1/cardinality for the normalized finite sampler, and instantiate the
parameter inequalities. Include any randomness and rejection introduced by
the actual builder. State the resulting success bound with valid inputs,
termination and all setup assumptions visible.

Acceptance: the composed algorithm has an explicit, nonvacuous numerical
failure bound for the paper's concrete parameter set, with no unbounded p2
term hidden in the conclusion.

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

Finally connect the FFA constraints and range checks to the curve formulas,
then to the builder and MSM loop. Account for lookup constraints, witness
bounds and exceptional branches present in the actual circuit.

Acceptance: concrete instances discharge the abstract interfaces; a composed
statement covers the intended circuit/procedure and parameters. Publish an
explicit list of any assumptions intentionally retained.

## Paper synchronization

After each step, update the formalization-status claims and theorem
hypotheses in the paper. Describe the present artifact as conditional
abstract MSM correctness plus range-bounded FFA constraint proofs until the
concrete composition is established. Keep scalar-window ordering consistent
with the big-endian traversal. Explain separately which counterexamples
exposed inconsistent assumptions, which exposed an unverified algorithm
stage, and which were merely unused library defects.

Suggested review units: build/CI; sampler normalization and instantiation;
table builder; quantitative rejection bound; concrete curve; concrete FFA
parameters and CRT; circuit composition and final paper claims.
