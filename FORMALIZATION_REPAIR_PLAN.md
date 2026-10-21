# Repair plan for the FFA and MSM formalization

Status: 2026-10-21, following the axiom repair in commit c0ed96d.
Cleanup, a full local proof check and the abstract sampler-normalization
repair are implemented. Guarded table construction and its composition
with MSM are now checked at the abstract group level. Environment
provisioning/CI and concrete instantiations remain open. The constructed
algorithm now has a checked symbolic rejection bound. Circuit instantiation
is outside the requested scope.
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

This remains a guarded algorithm in the abstract group model. Its rejection
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
abstract MSM correctness plus range-bounded FFA constraint proofs until the
concrete composition is established. Keep scalar-window ordering consistent
with the big-endian traversal. Explain separately which counterexamples
exposed inconsistent assumptions, which exposed an unverified algorithm
stage, and which were merely unused library defects.

Suggested review units: build/CI; sampler normalization and instantiation;
table builder; quantitative rejection bound; optional concrete curve and FFA
parameters/CRT; final paper claims. Circuit composition is out of scope.
