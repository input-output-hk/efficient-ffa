# Independent Lean formalization of efficient foreign-field arithmetic

A fresh development from the mathematical statements in
[Efficient Foreign-Field Arithmetic in PLONK](https://eprint.iacr.org/2025/695).
This project is separate from the existing EasyCrypt checkout and the supplied
Lean artifact. The multiplication milestone is complete; the remaining migration is planned below.

## Source policy

- The downloaded paper is the primary specification. Record ambiguities and
  corrections explicitly; do not silently turn a corrected algorithm into a
  claim about the literal published algorithm.
- Lean and mathlib are permitted foundations. The initial dependency checkout
  was copied from a pristine standard-library cache, not from the supplied
  formalization. No other project's proof sources were copied.
- The supplied Lean repository and archive are not consulted when authoring
  this development. They were not opened during the foundation or multiplication implementations.
- Earlier artifact reviews are background context. Independence here means
  fresh definitions and proof development, not a claim that prior reviews
  never happened. The EasyCrypt coverage inventory can guide priorities;
  its proof scripts are not the implementation template.
- A later comparison with existing artifacts should be a separate review,
  after the independent milestone has been written and checked.

The local paper used for this start is the 13-page PDF downloaded as
2025-695.pdf, with SHA-256:

~~~text
c075bb9c3db566eb579495e64eb074c2783cdba34dcd1417132eb5756e7b36dd
~~~

## Build and trust boundary

Lean is pinned to 4.31.0 and mathlib to
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. The Lake manifest pins transitive
dependencies. With elan installed, run:

~~~sh
lake exe cache get
lake build
~~~

The cache command downloads the standard mathlib build artifacts on a fresh
checkout. The local development already has that cache. The default build
checks both the library and Tests; warnings are treated as errors. This is
local build setup. CI and larger/production instances remain skipped.

All 24 library theorems compile, and their axiom reports contain
only Lean's standard propext, Classical.choice and Quot.sound. There are no
project axioms, admissions or native_decide proofs. The build uses supplied
mathlib artifacts; it is not a fresh rebuild of the entire standard library.

## Current checked results

| File | Result |
|---|---|
| [Arithmetic.lean](EfficientFFA/Arithmetic.lean) | A concrete finite LCM, equivalence with simultaneous congruences, and bounded reconstruction |
| [Limbs.lean](EfficientFFA/Limbs.lean) | Integer limb evaluation, product expansion, modular coefficient reduction, quotient characterization, reconstruction corollary, and integer linearity |
| [Multiplication/Definitions.lean](EfficientFFA/Multiplication/Definitions.lean) | Concrete parameters, coefficient reductions, quotient shifts, ranges, and native-modulus checks |
| [Multiplication/Bounds.lean](EfficientFFA/Multiplication/Bounds.lean) | Weighted-sum bounds, signed quotient intervals, and all four residual bounds |
| [Multiplication/Soundness.lean](EfficientFFA/Multiplication/Soundness.lean) | Auxiliary coefficient correspondence and soundness of the actual constraints |
| [Multiplication/Completeness.lean](EfficientFFA/Multiplication/Completeness.lean) | Explicit quotient witnesses, their ranges, and completeness |
| [Multiplication.lean](EfficientFFA/Multiplication.lean) | Acceptance iff modular multiplication, and canonical-output corollary |
| [Multiplication regressions](Tests/Multiplication.lean) | Full small parameter instances, explicit witnesses, rounding, noncanonical outputs, and incomplete-check counterexample |
| [Foundations.lean](Tests/Foundations.lean) | Noncoprime/signed/zero moduli, strict-bound boundary, a radix-10 multiplication example, signed limbs, and theorem-axiom reports |

Limbs are finite vectors of integers, with well-formedness expressed as a
separate predicate. This avoids abstract word/array axioms and permits both
ordinary bounded limbs and future signed or unreduced limbs. The radix is
an integer parameter, not implicitly a power of two. The initial algebraic
lemmas hold even without positivity assumptions; the encoded-constraint
theorems explicitly require the appropriate positive parameters.

## Multiplication correspondence and deliberate differences

The source for this milestone was the downloaded PDF, Section 3.1,
equations (1)-(4), and Theorems 3.1-3.2. No existing FFA proof scripts
were consulted. Definitions and endpoint statements were checked against
those equations after completing the proofs.

| Paper claim | Lean endpoint | Required hypotheses |
|---|---|---|
| Theorem 3.1: soundness | Parameters.multiplication_sound | Positive parameters, NoWrap, bounded x/y/z, and Accepts |
| Theorem 3.2: completeness | Parameters.canonical_witnesses_accept and Parameters.multiplication_complete | Positive parameters, WidthBounds, bounded x/y/z, and correct modular product |
| Both directions together | Parameters.accepts_iff_multiplication | Valid parameters and bounded x/y/z |
| Canonical result, as an additional corollary | Parameters.canonical_output | Soundness hypotheses and 0 <= eval B z < q |

All endpoints above are in namespace EfficientFFA.Multiplication.
Parameters.Accepts contains the witness ranges and exactly the native and
auxiliary congruence checks modulo p. Limb ranges are separate explicit
premises, including the output range checks. Residual bounds and congruences
modulo auxiliary moduli are derived, not assumed at the endpoints.

The equivalence therefore proves the multiplication constraint system on
supplied limb vectors. It does not prove circuit wiring, range-check gadgets,
or an implementation of field elements. Integer congruences express the
arithmetic semantics of the checks; a concrete ZMod/circuit bridge is separate.

Deliberate generalizations and conventions:

- Indices are Fin n (0 through n-1), with little-endian evaluation. The
  theorem prose in the PDF has an inclusive n subscript inconsistent with
  its sums; we follow the sums and its n-limb representation.
- B, p and q are positive integers; primality and a power-of-two radix are
  unnecessary for these arithmetic statements. The PDF theorem also states
  positive integers. Finite families allow repetitions, noncoprime moduli,
  and an empty auxiliary family when its reconstruction conditions hold.
- The paper assumes positive n and q <= B^n. These are unnecessary for a
  theorem about an already supplied bounded triple; no claim that arbitrary
  residues have limb representations is made here.
- Widths need not be minimal powers of two. They must satisfy WidthBounds,
  and their actual values enter NoWrap. Increasing a width can invalidate
  NoWrap, so larger widths are not unconditionally safe.
- Lower quotient endpoints are -(A/q) and -(Am/m), with division performed
  before negation. This implements ceiling of the negative rational lower
  bound. Upper endpoints use floor, including when Cm is negative. If the
  paper's truncation-toward-zero convention is applied to a negative Cm/m,
  it gives a weaker upper bound: our floor bound remains valid, and any
  width covering that larger interval also covers ours. A regression checks
  Cm = -60, m = 100, and lmax = -1 explicitly. This distinction affects
  sufficient width selection, not the constraint equations.
- Native no-wrap and LCM conditions are needed only for soundness; adequate
  witness widths are needed only for completeness. Valid combines them for
  the paper-style public equivalence.
- Bounded limbs do not imply a canonical residue. An accepting output can
  evaluate to q; the canonical-output corollary deliberately has the extra
  value-range premise.

The regressions prove satisfiability of complete numerical parameter bundles,
including radix 3, composite q = 8, auxiliary moduli 2 and 4, and different
auxiliary widths. A separate valid bundle exhibits a false product passing
its native check alone, while the full system rejects every possible bounded
witness for that triple. These are small arithmetic regressions, not production
parameter recommendations.

## Execution plan

Baseline and milestone update: 2026-10-27. Steps 1-4 are **complete**: the
library and regressions build with warnings as errors, all library theorem
axiom reports use only the standard Lean axioms, and the paper correspondence
is recorded above. Their original implementation checklist is retained below.
Steps 5-7 remain planned work. The next milestone is lazy arithmetic and
normalization in Section 3.2; integer linearity alone does not cover it.

### 1. Fix the multiplication specification (complete)

Implemented module: EfficientFFA/Multiplication/Definitions.lean.

Define parameters and witnesses directly from the paper:

- An integer radix B > 0, foreign modulus q > 0, native modulus p > 0,
  and n limbs. Do not require primality for integer congruence results.
- A finite family indexed by Fin r, with M i > 0. Repeated and noncoprime
  moduli are allowed. No nonempty-family premise unless a proof needs it.
- A native witness width t and individual auxiliary widths tm i, all natural
  numbers. Write Umax = 2^t and Vmax i = 2^(tm i).
- Witnesses u : Int and v : Fin r -> Int, with their explicit range predicates.
- Separate predicates for numerical parameter conditions and accepted
  constraints. Acceptance must contain the actual native-field equations,
  not the multiplication result or an assumed integer residual bound.

Use the existing mulResidual definition, calling it D below. Define the
unshifted bounds and quotient endpoints:

~~~text
A    = (B-1) * sum_i (B^i mod q)
C    = (B-1)^2 * sum_i sum_j (B^(i+j) mod q)
kmin = -(A / q)
kmax = C / q
R    = D(x,y,z) - (u+kmin)*q
~~~

All divisions above are integer floor divisions with positive denominator.
In particular, -(A/q) is the ceiling of -A/q, not floor(-A/q).

For each auxiliary modulus m = M i, define:

~~~text
Am = (B-1)*sum_j (B^j mod q mod m)
     + Umax*(q mod m) + (kmin*q mod m)
Cm = (B-1)^2*sum_j sum_k (B^(j+k) mod q mod m)
     - (kmin*q mod m)
lmin = -(Am / m)
lmax = Cm / m

E = sum_j sum_k (B^(j+k) mod q mod m)*x_j*y_k
    - sum_j (B^j mod q mod m)*z_j
    - u*(q mod m) - (kmin*q mod m)
Aux = E - (v_i+lmin)*m
~~~

The native check is R = 0 modulo p; every auxiliary check is Aux = 0
modulo p. State any representation-coverage requirement q <= B^n separately:
the multiplication theorem on already supplied bounded limb vectors does
not need to assume every residue is representable.

Completion gate: review these definitions and the proposed endpoint
statements against paper equations (1)-(4) and Theorems 3.1-3.2. Record
indexing or rounding discrepancies explicitly. Do not introduce unfinished
proof declarations merely to display proposed statements.

### 2. Derive the tight bounds and quotient intervals (complete)

Implemented module: EfficientFFA/Multiplication/Bounds.lean; reusable integer
division lemmas may extend Arithmetic.lean.

Prove from well-formed limbs that -A <= D <= C. Derive quotient bounds
when D = k*q, then show that u = k-kmin satisfies 0 <= u < Umax under
kmax-kmin < Umax. Prove these bounds from the weighted coefficient sums,
not from the coarser n^2*B^2*q estimate.

For each auxiliary expression, prove -Am <= E <= Cm for bounded u.
If E = l*m, derive lmin <= l <= lmax and the range of v_i = l-lmin.
For arbitrary bounded witness values, derive:

~~~text
-Am - (Vmax i + lmin)*m <= Aux <= Cm - lmin*m
-A - (Umax+kmin)*q     <= R   <= C - kmin*q
~~~

The numerical conditions must explicitly include the width bounds
kmax-kmin < Umax and lmax_i-lmin_i < Vmax i, together with
-p < -Am-(Vmax i+lmin_i)*(M i) and Cm-lmin_i*(M i) < p for each i.
The two LCM conditions are stated in the soundness step below.

Keep the algebraic bound lemmas independent of their eventual use in
soundness or completeness. Any strengthening of a strict endpoint must
be proved rather than inferred from the paper's informal rounding prose.

Completion gate: every required inequality follows from limb ranges and
explicit parameter conditions; none is assumed as a global axiom or as an
unproved property of a witness constructor.

### 3. Prove multiplication soundness (complete)

Implemented module: EfficientFFA/Multiplication/Soundness.lean.

The proof should establish these connections explicitly:

1. Aux is strictly between -p and p by the numerical conditions, so the
   auxiliary check modulo p implies Aux = 0 over the integers.
2. Reducing the original R modulo m agrees with the corresponding
   coefficient-reduced expression E. Hence Aux = 0 implies R = 0 modulo m.
3. Combine those congruences with the native check using the proved finite
   LCM theorem. If L = LCM(p :: auxiliary moduli), require
   A+(Umax+kmin)*q < L and C-kmin*q < L to establish -L < R < L.
4. Reconstruct R = 0 and apply the existing quotient characterization to
   conclude eval B x * eval B y = eval B z modulo q.

Completion gate: the public soundness theorem starts from well-formed
limbs, numerical parameter conditions and the actual encoded constraints.
It must not retain the residual congruences or residual bounds as extra
unproved premises. Its axiom report contains only the standard Lean axioms.

### 4. Construct completeness witnesses and close the milestone (complete)

Implemented module: EfficientFFA/Multiplication/Completeness.lean, with a
Multiplication.lean entry point exposing the final results.

Given a correctly multiplying triple, construct witnesses explicitly:

~~~text
k   = D / q
u   = k - kmin
l_i = E_i / (M i)
v_i = l_i - lmin_i
~~~

Prove the required divisibilities before using the divisions as exact
quotients. Derive all witness ranges and show that the native and auxiliary
residuals are zero over the integers, hence also modulo p.

Separate assumptions actually needed for this construction from conditions
used only by soundness: the internal completeness proof should not need
LCM reconstruction or native no-wrap inequalities. Provide a wrapper under
the paper's combined parameter conditions and the final equivalence:

~~~text
For well-formed x, y, z and valid numerical parameters:
  (exists bounded witnesses satisfying the encoded constraints)
    iff eval B x * eval B y = eval B z modulo q.
~~~

Add a canonical-output corollary with its extra output range premise.
Do not assume primality or canonical inputs just to simplify the proof.

Validation belongs in Tests/Multiplication.lean and must cover:

- Zero and maximal limbs, negative quotient witnesses before shifting, and
  a non-divisible lower-bound numerator that distinguishes floor from ceiling.
- Different auxiliary witness widths, noncoprime auxiliary moduli, a
  non-power-of-two radix, and positive composite foreign moduli.
- Strict no-wrap endpoints and an incorrect product passing an incomplete
  set of checks, when a small explicit counterexample is available.
- A small satisfiable full parameter set and actual bounded witnesses,
  demonstrating that the final theorem's hypotheses are jointly realizable.
- Noncanonical output representatives, distinguishing modular correctness
  from the canonical-output corollary.

Acceptance: lake build checks the library and regressions with warnings as
errors; final theorem-axiom reports contain no project axioms or admissions;
the README maps each endpoint theorem to the paper and lists every deliberate
difference. This closes milestone 1. A small regression instance does not
reopen the skipped work on larger or production parameter sets.

### 5. Formalize lazy arithmetic and normalization

This starts only after the multiplication milestone is complete.
Proposed modules: LazyArithmetic.lean and Normalization.lean.

Use the existing integer limb vectors with explicit per-limb lower and
upper bounds. Prove the Table 1 rules for addition, subtraction, negation,
constant addition and constant multiplication, including negative constants.
Model the relation between the tracked integer limbs and their native-field
residues: a canonical residue must not silently be interpreted as a signed
integer. State when a lift is unique and when only a representation relation
is required.

Define equation (5)'s normalization constraints and derive their own quotient,
auxiliary and reconstruction bounds. Reuse the integer reconstruction and
quotient-interval lemmas without forcing normalization into a multiplication
statement. Prove soundness, bounded witness existence and preservation of
the foreign-field value. Include representability conditions needed to
construct normalized output limbs.

Then derive division, inversion and comparison results. For arbitrary q,
use invertibility rather than mere nonzeroness; specialize the criterion to
nonzero elements only under the necessary prime-field hypothesis.

Acceptance: checked bounds and native-residue correspondence for the lazy
operations, followed by normalization soundness/completeness and their
composition. Integer linearity alone does not meet this completion gate.

### 6. Prove the unique-zero representation

Proposed module: ShiftedEncoding.lean, after the unshifted arithmetic is stable.
Define 1 + eval B x modulo q. Under well-formedness and q <= B^n < 2*q,
prove that zero forces eval B x = q-1 and that its bounded limb vector is
unique. Establish representability and injectivity where needed.

Derive the modified multiplication identity, changed limb-wise operations
and the zero-test criterion. Recheck the quotient and residual bounds for
the extra linear terms; do not reuse the unshifted bounds without proof.
Acceptance includes boundary examples where removing the size or limb-range
condition permits a second zero representation.

### 7. Develop EC and MSM mathematics independently

First specify affine addition/doubling equations and their exceptional cases,
then connect them to a concrete group type or an explicit representation
structure. Use ordinary theorem hypotheses, not global project axioms.
Prove the repeated-base table argument and distinguish implied table guards
from the guards required in the varying-addend MSM loop.

Next prove the random-offset invariant, full mathematical witness composition,
and soundness. For little-endian windows, process indices in descending order
and record the discrepancy with the published forward traversal. Model the
sampler as an explicitly normalized finite distribution and derive the
failure bound; keep invertibility and cardinality conditions visible.

Acceptance: coordinate-level soundness and witness existence, corrected MSM
soundness and statistical completeness, and explicit representation/sampler
obligations. A generic conditional theorem must be labelled as such.

### Scope boundary and review discipline

The native-field encodings of the four custom EC identities in Section 4.1
remain a separate scope decision. Record this gap even after proving the EC
and MSM mathematics. Those equations' coordinate-level meaning is distinct
from their implementation with limbs and auxiliary moduli.

At each milestone, review statements against the paper before polishing proof
scripts, run the local build, inspect theorem axioms, and update the coverage
record. An artifact comparison with the supplied Lean project remains a
separate, explicitly requested review after an independent milestone is checked.

PLONK wiring, Halo2 correspondence, gate counts, benchmarks, CI and larger
parameter instances remain outside the current work. Paper edits are deferred.
The existing EasyCrypt repository and historical release are preserved.
