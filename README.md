# Independent Lean formalization of efficient foreign-field arithmetic

A fresh development from the mathematical statements in
[Efficient Foreign-Field Arithmetic in PLONK](https://eprint.iacr.org/2025/695).
This project is separate from the existing EasyCrypt checkout and the supplied
Lean artifact. The multiplication, lazy-arithmetic/normalization, and unique-zero milestones
are complete. Coordinate-level elliptic-curve operations, precomputed tables,
and parameter-dependent table witness existence are checked. The corrected
MSM group loop, normalized rejection bound, and full coordinate-trace
soundness and statistical completeness are also checked, under the explicit
parameter conditions and documented algorithm refinements below.

The [paper-to-Lean audit](PAPER_AUDIT.md) records the claim-by-claim coverage,
remaining representation gaps, and confirmed differences from the printed
algorithms, including an additional Figure 3 infinity-branch overlap.

## Source policy

- The downloaded paper is the primary specification. Record ambiguities and
  corrections explicitly; do not silently turn a corrected algorithm into a
  claim about the literal published algorithm.
- Lean and mathlib are permitted foundations. The initial dependency checkout
  was copied from a pristine standard-library cache, not from the supplied
  formalization. No other project's proof sources were copied.
- The supplied Lean repository and archive are not consulted when authoring
  this development. They were not opened during the foundation, multiplication, normalization, shifted-encoding, EC, or initial table implementations.
- Earlier artifact reviews are background context. Independence here means
  fresh definitions and proof development, not a claim that prior reviews
  never happened. The EasyCrypt coverage inventory can guide priorities;
  its proof scripts are not the implementation template.
- At the user's explicit request on 2026-10-27, the checked table milestone
  was compared with the EasyCrypt table and rejection proofs. That comparison
  informed the subsequent parameter-selection stage; details are recorded below.
  The supplied Lean artifact remains unconsulted.

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

All 216 library theorems compile, and their axiom reports contain
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
| [Trace regressions](Tests/Trace.lean) | Accepted concrete curve traces, wrong output, broken initial linkage, and a nonempty execution returning infinity |
| [MSM regressions](Tests/MSM.lean) | Unequal windows, accepted execution, exact excluded-seed counts, instantiated probability theorem, and noninvertible coefficient |
| [Table regressions](Tests/Tables.lean) and [parameter regressions](Tests/Parameters.lean) | Accepted concrete table, known rejected offsets, prime/composite group parameters, and failure without scalar invertibility |
| [EC regressions](Tests/EllipticCurve.lean) | Concrete order-two/order-three points, missing-precondition counterexample, and distinct infinity encodings |
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

## Lazy arithmetic and normalization correspondence

This milestone follows Section 3.2, Table 1 and equation (5), directly from
the same PDF. The supplied Lean artifact and EasyCrypt proofs were not opened.
The normalization proof reuses the structure and reusable lemmas of our own
independent multiplication development. The paper explicitly omits the
auxiliary details for normalization; the checked definitions provide those
details, rather than claiming to transcribe an algorithm fully printed there.

| Paper claim | Checked result |
|---|---|
| Table 1 bound propagation | LazyArithmetic.bounded_add/sub/neg/add_constant/scale, with inclusive per-limb endpoints and swapped endpoints for negative constants |
| Native limb operations preserve their tracked meaning | LazyArithmetic.represents_add/sub/neg/add_constant/scale; existing integer evaluation linearity and eval_neg give the foreign arithmetic meaning |
| Equation (5) preserves the foreign value | Normalization.Parameters.normalization_sound and accepts_iff_normalization |
| Normalization witnesses exist | canonical_witnesses_accept and normalization_complete for supplied equivalent outputs; normalization_exists also constructs an output under q <= B^n |
| Signed native wraparound is compatible with normalization | accepts_of_rep, stored_normalization_sound, stored_normalization_exists, and subtraction_normalization_sound |
| Division and inversion through multiplication | Division.division_iff, encoded_division_iff, encoded_inverse_iff, and inverse_exists_iff_coprime |
| Inverse-of-difference witnesses test disequality over a prime modulus | Division.prime_inverse_iff and prime_disequality_iff |

Normalization endpoint names in the table are in namespace
EfficientFFA.Normalization.Parameters. The representation relation is
pointwise congruence between stored native values and tracked signed integers.
All five operations preserve that relation using just their native equations;
there are no new per-operation range-check premises. Bounds propagate from
known input bounds. To apply normalization, the resulting tracked bounds
must fit [-limit, limit], and the normalization parameters must satisfy their
explicit width and no-wrap conditions.

This distinction matters: -1 can be stored as p-1, but evaluating p-1 as an
ordinary foreign integer generally gives the wrong answer. The bridge theorem
transports the actual normalization checks to the tracked signed input before
using integer residual bounds. It does not require stored representatives to
lie in the signed input interval. A separate lift_unique theorem proves
uniqueness when every inclusive interval has width strictly less than p;
representation and normalization do not silently assume that uniqueness.

For normalization, write S = sum_i (B^i mod q). The checked residual bounds
are exactly the paper's conservative linear bounds:

~~~text
D = sum_i (B^i mod q) * x_i - sum_i (B^i mod q) * z_i
-(limit+B)*S <= D <= limit*S
~~~

For each auxiliary modulus m, put Sm = sum_i (B^i mod q mod m). The auxiliary
coefficient expression has lower bound -Am and upper bound Cm, with:

~~~text
Am = (limit+B)*Sm + 2^t*(q mod m) + (kmin*q mod m)
Cm = limit*Sm - (kmin*q mod m)
~~~

The quotient shifts, width conditions, auxiliary no-wrap checks and LCM
reconstruction have the same form as multiplication, using these linear
bounds. They are derived from signed input bounds and bounded output limbs,
not by applying a multiplication theorem to out-of-range inputs. As before,
soundness needs NoWrap, completeness needs WidthBounds, and the combined
Valid predicate packages both. The canonical-output existence theorem also
requires q <= B^n. No-wrap is unnecessary to construct the witnesses.

The division results distinguish invertibility from nonzeroness. For arbitrary
integer q, the criterion is IsCoprime a q; for positive prime q, it is precisely
a nonzero residue. The regression at q = 8 proves that 2 is nonzero but has no
inverse, and that the naive division equation has distinct solutions.
The disequality result is the mathematical inverse-of-difference criterion;
it is not a standalone circuit implementation of comparison. Its subtraction
and normalization stages are covered separately by the checked composition
and representation lemmas above. No order-comparison claim is made.

The full signed regression uses radix 3, limit 5, q = 8, p = 131, auxiliary
moduli 2 and 4, and different witness widths. It checks stored input [130,0]
representing tracked [-1,0], normalization to [1,2] (value 7), and actual
quotient witnesses. Further examples exercise both signed endpoints and
prove rejection of output zero for that input, irrespective of witnesses.

## Unique-zero and shifted-arithmetic correspondence

This milestone follows Section 3.2.4 of the same downloaded paper. No supplied
Lean sources or EasyCrypt proof scripts were consulted. Its shifted value is
value B x = 1 + eval B x, reduced modulo q when interpreted as a foreign value.

| Paper claim | Checked result in EfficientFFA.ShiftedEncoding |
|---|---|
| Zero has exactly one bounded representation | exists_unique_zero under B > 0, q > 0 and q <= B^n < 2*q |
| Zero corresponds to the unshifted integer q-1 | zero_iff_eval, with eval_bounds and eval_injective supplying the representation facts |
| A limb-wise zero comparison is sufficient | zero_iff_limbs; zero_iff_native_checks also covers comparisons modulo p under B <= p |
| Every foreign value has a shifted representation | exists_representation under q <= B^n |
| Shifted operations need low-limb corrections | value_add/sub/neg/add_constant/scale, bounded operation lemmas, and represents operation lemmas |
| Normalization is unchanged | value_congr_iff, normalization_iff, stored_normalization_sound and stored_normalization_exists |
| Modified multiplication with extra linear terms | Multiplication.shifted_product_identity and Multiplication.Parameters.accepts_iff_multiplication, with full soundness and explicit witness construction |

The native zero-test theorem keeps limb ranges explicit. B <= p ensures that
congruence modulo p distinguishes bounded limb values. It is a numerical
parameter condition, not an additional per-operation check. No primality is
needed for zero uniqueness, shifted arithmetic or these constraint proofs.
Zero uniqueness does not imply uniqueness for other residues: the regressions
include two different bounded representations of one.

For vectors with at least one limb, only the least significant limb receives
the following corrections to the ordinary limb-wise operation:

| Operation | Low-limb correction |
|---|---|
| Addition of two shifted operands | +1 |
| Subtraction of two shifted operands | -1 |
| Negation | -2 |
| Multiplication by an integer constant c | c-1 |
| Addition of a plain integer constant c | c (directly to the existing low limb) |

Addition of a constant supplied in shifted limb form uses the ordinary shifted
addition operation. The arithmetic lemmas prove exact integer identities;
bounds may grow and become negative, so normalization remains necessary before
operations requiring well-formed inputs. The stored-residue lemmas carry the
same interpretation through native-field arithmetic. The selected normalized
shifted representative has integer value 1 + ((value B x - 1) mod q), lying
in [1,q]; q represents zero. It is not a canonical integer in [0,q).

The shifted multiplication residual adds both reduced linear terms to the
unshifted residual. If A = (B-1)*sum_i(B^i mod q), its lower bound stays -A,
while its upper bound becomes:

~~~text
C_shifted = (B-1)^2 * sum_i sum_j(B^(i+j) mod q) + 2*A
~~~

For each auxiliary modulus m, its upper bound similarly gains
2*(B-1)*sum_i(B^i mod q mod m). The lower bound has the same algebraic form,
but uses the actual selected native witness width. All quotient endpoints,
width checks, native no-wrap inequalities, and LCM conditions use these shifted
bounds. They are proved independently from limb ranges; no old upper-bound
claim is reused. The paper prints the modified identity but not this full
parameter derivation; these checked bounds supply that missing detail.

The multiplication proof itself does not need the unique-zero capacity upper
bound B^n < 2*q. That condition belongs to zero uniqueness. The optional
multiplication_exists theorem requires q <= B^n to construct an output,
whereas completeness for a supplied correct triple does not. A full small
instance uses radix 3, q = 8, p = 131, noncoprime auxiliary moduli 2 and 4,
and different auxiliary widths. A maximal input attains shifted residual 48,
strictly exceeding the unshifted bound 32. Tests also reject the answer obtained
by forgetting the shift, for all possible bounded quotient witnesses.

Boundary regressions exhibit two zero representations when B^n = 2*q,
nonunique expansions without limb bounds, and false native zero comparisons
when the radix is larger than the native modulus. Circuit wiring and concrete
range-check gadget implementations remain outside scope.

## Coordinate-level elliptic-curve results and Figure 3 limitation

This stage uses Sections 4.2-4.4 and Figures 1-3 of the downloaded paper,
plus mathlib's standard WeierstrassCurve.Affine modules (Basic, Formula and
Point). The supplied FFA Lean artifact and EasyCrypt proofs were not consulted.
Curve specifies a, b and a proof that the concrete short-Weierstrass
model's discriminant is nonzero. Its Point type is mathlib's actual group of
nonsingular curve points; no project-specific group-law axioms are introduced.
A concrete smooth curve over ZMod 7 realizes the hypotheses in regressions.

| Contract | Checked guarantee |
|---|---|
| AddChecks and distinct input x-coordinates | addition_sound derives output curve membership and equality to the concrete group sum; addition_complete constructs the slope and output |
| DoubleChecks and input curve membership | doubling_sound derives output membership and the group double, with no extra denominator or output-x inequality premise |
| Existence of finite doubling witnesses | doubling_witnesses_iff is equivalent to 2*y != 0; double_eq_zero_iff identifies the excluded inputs as nonidentity points whose double is zero |
| Figure 1 with Boolean infinity tags | flagged_double_sound and flagged_double_witnesses_iff handle arbitrary ignored coordinates at infinity; a local no-two-torsion hypothesis suffices for completeness |
| Figure 2 with Boolean infinity tags | incomplete_sound/complete retain its finite-input and distinct-x preconditions explicitly |
| Ordered complete addition | complete_sound/exists/correct prove group correctness and output existence for every valid pair, including infinity and order-two points |

The last output equation is linear in y(R): it fixes
 y(R) = slope*(x(P)-x(R))-y(P)
without division by x(R)-x(P). Thus the order-three exclusion discussed in
Section 4.3 is unnecessary for these coordinate constraints. The checked
ZMod 7 example has P=(0,1), 3P=0 and 2P=(0,6): the output x-coordinate equals
the input x-coordinate, yet the doubling checks accept the correct output.
By contrast, the order-two point (3,0) doubles to infinity and has no witnesses
for Figure 1's finite-output branch. This is a completeness limitation, not
an accepted incorrect double. At a smooth input, the tangent equation itself
implies a nonzero denominator whenever witnesses are accepted.

### Literal identity-copy implications are not complete for arbitrary infinity encodings

Section 4.2 allows infinity to have arbitrary ignored coordinates. Section
4.4.2 expands Figure 3's two identity implications into coordinate-copy
constraints. Taken simultaneously as printed, if both inputs are infinity,
Step 3 requires R=Q and Step 4 requires R=P, including their coordinates.
Distinct infinity encodings therefore have no output satisfying even these
two necessary conditions. identity_copies_iff proves that, when both tags are
true, such an output exists exactly when the two encodings are identical.
The regression uses valid encodings (0,0,true) and (1,1,true), proves that both
decode to the same group identity, and proves that no literal copy output exists.

The later [audit](PAPER_AUDIT.md#f3-figure-3s-overlapping-implications-are-not-complete-for-all-allowed-infinity-encodings)
also confirms a conflict with only one infinity input if the inverse predicate
is implemented by the coordinate-only test stated in Section 4.4.2. The ignored
coordinates of infinity can equal the negative of a finite input. The identity
copy then requires a finite output while Step 5 requires infinity.
Tests/PaperAudit.lean checks this case and the existing ordered refinement.

The new CompleteAccepts contract is deliberately labelled a refinement:
choose the left-identity branch first, then the right-identity branch; for
finite inputs, handle inverses, equal points, and distinct x-coordinates.
Its alternatives use the actual coordinate equations, not an assumed group
sum. Soundness derives output validity and the sum. This ordering resolves
the infinity-copy conflict and handles finite order-two inputs in the inverse
branch. No claim of completeness for the literal conjunction of all Figure 3
implications is made. An alternative design could impose canonical infinity
coordinates, but that would be an extra representation invariant and is not
assumed here. The paper itself has not been edited.

Infinity flags are Bool values, making bitness explicit at the mathematical
level. These results are over foreign-field coordinates; the native-field
encodings of the four EC identities, Boolean wiring and range-check gadgets
remain outside the current milestone. The repeated-base table and setup
parameter results are described next, followed by the loop and group-level
probability theorem and full supplied-coordinate-trace composition.

## Precomputed tables and parameter selection

TableChecks contains only the repeated Figure 2 coordinate equations. From
on-curve base/start inputs and the single initial x-inequality, table_sound
and table_guards derive every later input's curve membership, group meaning,
and x-inequality. No per-step table checks are added. This argument does not
need global exclusions of two- or three-torsion. table_lookup_sound gives the
meaning of every in-range lookup: entry i = i*P - V.

For s > 0 additions (s+1 entries), table_safe_iff_avoids proves that the
admissible offsets are precisely those outside:

~~~text
badOffsets(P,s) = {0, P, ..., s*P} union {-P}
card(badOffsets(P,s)) <= s+2
~~~

The finite set deduplicates any coinciding multiples. table_complete builds
actual coordinates and slopes from admissibility, and offset_table_iff_avoids
relates avoidance to existence of the table equations' witnesses under the
initial guard. The familiar V=2P example is a rejected offset in this set;
it is not an accepted wrong table and does not motivate additional checks.

For l rows, the shared offset is V=s*U. badSeeds_card_le proves at most
1+l*(s+2) excluded seeds, including the zero seed. When both scalar maps
U -> s*U and U -> l*U are injective, avoiding this set gives all table
admissibility conditions and a nonidentity initial accumulator l*U.
exists_safe_setup derives these injectivity properties from coprimality with
the finite group cardinality and proves existence if:

~~~text
1 + l*(s+2) < card(G)
~~~

For s=2^w-1 with w>0, this is 1+l*(2^w+1) < card(G).
exists_safe_setup_prime proves that prime group cardinality, l>0, s>0 and
this size bound suffice; coprimality then follows rather than being assumed.
This is a sufficient parameter rule, not a necessary bound.
tables_exist_of_parameters applies the result to mathlib's concrete curve
group and produces all affine table witnesses, including the initial
x-inequalities. No offset-admissibility or per-step guard premise remains
in that endpoint. Its base inputs must be finite on-curve points.

These results cover setup and tables. The following loop stage extends them
to one seed avoiding all exceptional additions and a normalized probability
bound. Regressions instantiate setup parameters in
additive ZMod 17 and ZMod 25 and show why group size alone is insufficient
when the offset scalar is not invertible; these are small group examples,
not production curve recommendations.

### EasyCrypt comparison and provenance

The independent table proofs above were written and built before this
comparison. At the user's request, the EasyCrypt checkout was then consulted:
MSM_TableConstraints.ec (accepted_step_safe and accepted_table_row_safe),
MSM_TableConstruction.ec, MultiScalarMul_Abstract.ec,
MultiScalarMul_Abstract_Completeness.ec, MSM_RejectionBound.ec, and the
coordinate-trace and small-instance setup. Its scripts were not translated.
This comparison informed the parameter-selection statements in Parameters.lean.

The results agree on the central distinction: accepted table equations imply
the internal guards; unsuitable offsets affect witness existence and belong
in the rejection analysis. The existing varying-addend incompleteAddLoop in
MultiScalarMul_Abstract.ec retains xdiff checks, as does Figure 4 of the paper.
Those are existing algorithm checks, not proposed additions. The isolated
changing-addend regression only shows that the repeated-base proof cannot be
applied to arbitrary addend sequences; it does not replace the MSM parameter
and invariant analysis.

EasyCrypt's sampled_rejection_bound_cardinality bounds total failure by
(1+l*(2^w+1)+2*T*l)/card(G), with its explicit scalar-invertibility and ambient
loop coefficient conditions. The new Lean group-level probability theorem
now includes the same three contributions. During this next stage, Figure 4,
the EasyCrypt loop definitions, and the coefficient hypotheses in
MultiScalarMul_Abstract_Completeness.ec were reread to check correspondence.
The Lean recurrence, invariants, finite-set arguments and PMF proof were
written independently using mathlib; no EasyCrypt proof scripts were translated.

## MSM loop, parameter rules, and uniform rejection bound

Loop.lean defines the actual group recurrence: initialize l*U, multiply the
accumulator by b, then add each selected table entry digit*P-(b-1)*U.
loop_invariant proves that after each complete window, the accumulator is
its unshifted Horner value plus l*U. row_invariant gives the value before row
j as D + A*U, where D is independent of U and:

~~~text
A = b*l - (b-1)*j
~~~

loop_correct subtracts l*U and proves equality with the sum of the intended
little-endian scalars times their bases. It uses descending window indices.
This is an explicit correction to Figure 4's forward traversal when its
windows are little-endian. The generic recurrence allows any positive radix;
the paper's doubling implementation uses b=2^w. This group correctness theorem
alone does not certify arbitrary supplied affine witnesses.

For each actual intermediate accumulator and auxiliary, collision_iff isolates
the two bad cases acc=aux and acc=-aux. Their seed coefficients are:

~~~text
c_plus  = b*l + (b-1)*(1-j)
c_minus = b*l - (b-1)*(1+j)
~~~

Both are positive for 0 <= j < l and b>0, and at most b*l+b-1.
Injectivity of their scalar maps gives at most two excluded seeds per
addition, hence loopBadSeeds_card_le proves the 2*T*l contribution. Together
with setup, the counted set has size at most:

~~~text
failureBudget = 1 + l*(b+1) + 2*T*l
~~~

GroupAccepts states initial nonidentity, table admissibility, and absence of
those collisions in the defined loop. uniform_group_failure_bound proves
that its failure probability is at most failureBudget/card(G), using mathlib's
normalized PMF.uniformOfFintype. The event is measured by its outer measure;
on a finite space this gives the ordinary probability of the event without
requiring a separate measurable-space instance. The bases and digits are fixed
before sampling U. No independence between individual collision events is
assumed: the finite union bound permits arbitrary overlap.

The prime-cardinality wrapper requires b>1, l>0, and:

~~~text
q = card(G) is prime
b*l+b-1 < q
~~~

These numerical conditions imply injectivity of all collision coefficients,
the setup scalars b-1 and l, and the radix b. They are sufficient conditions,
not optimal ones. If failureBudget < q as well, exists_groupAccepts_prime
proves a suitable seed exists. Unlike the count-only setup milestone, the
uniform bound here is a theorem about an explicitly normalized distribution.

With in-range digits, row_ready derives nonidentity and distinct/opposite
operand preconditions at every addition. loop_ne_zero and doubling_ready
prove finiteness of window boundaries and all intermediate doublings.
msm_row_witnesses and msm_double_witnesses turn these results into actual
affine equations on mathlib's concrete curve group, using canonical coordinates
of the group execution. They introduce no additional table checks or tangent
guards. The radix-injectivity premise is discharged by prime_radix_injective
under the same numerical rule above.

The regression in additive ZMod 17 uses b=4, l=1, T=2 and little-endian
windows [1,2]. It checks an accepted seed U=5, the result 9 (versus 6 for
forward traversal), four loop exclusions, nine total exclusions, and the
10/17 probability upper bound. A ZMod 5 example shows a noninvertible
coefficient with five solutions, making the coefficient condition substantive.
These are small group regressions, not production curve instances.

## Full coordinate-trace soundness and statistical completeness

This stage composes the independently proved table, group-loop and local
coordinate results above. It uses those local modules and mathlib; no further
EasyCrypt or supplied Lean sources were consulted for these proofs.

CoordinateTrace contains the supplied seed, offset, constant-multiplication
chains, tables, window boundaries, doubling states, row states and output.
TraceAccepts contains only coordinate conditions and index ranges:

- Seed curve membership and complete-add chains enforcing V=(2^w-1)*U and
  the initial accumulator l*U, with equality to their supplied endpoints.
- Each table's initial entry -V, its single initial x-guard and its raw
  incomplete-add equations. No internal table guards are added.
- Window range checks, exact lookup linkage, doubling equations, and the
  varying-addend loop's existing x-guards and addition equations.
- Equalities connecting each segment to the next, and the final complete
  addition with the opposite of the initial accumulator.

On-curve finite bases are explicit input premises. No point's intermediate
curve membership, group sum, table value, or final MSM value is assumed in
TraceAccepts. trace_setup derives the constant meanings; trace_lookup derives
validity and meaning of the selected entry; trace_doubles, trace_rows and
trace_boundaries propagate group meaning through the supplied coordinates.
trace_sound proves agreement with the group recurrence. The public
trace_sound_littleEndian endpoint proves the intended scalar MSM for every
accepted supplied trace, with descending traversal. Soundness does not
require prime group order or the statistical-completeness parameter bounds.

trace_complete constructs an entire linked trace from GroupAccepts,
in-range windows, positive w/l, and radix injectivity. Constant chains are
constructed using complete addition; tables and loop states use the concrete
curve group's canonical affine coordinates, with all equation witnesses
proved to exist. The final operation uses the already documented ordered
CompleteAccepts refinement and permits infinity. TraceWitnesses ties the
trace's seed coordinates to the sampled group point; this semantic relation
is outside the coordinate-only acceptance contract.

uniform_littleEndian_trace_failure_bound_prime transfers the normalized bound
to the event that no complete coordinate trace exists for the sampled seed:

~~~text
Pr[no accepted trace for U] <= (1+l*(2^w+1)+2*T*l)/card(C.Point)
~~~

It requires finite prime curve-group cardinality q, w>0, l>0, finite
on-curve bases, in-range fixed windows, and (2^w)*l+2^w-1 < q.
The same normalized PMF samples all curve-group points, including the identity;
the identity seed is already included in the exclusion budget. No additional
admissibility premise is left to the caller. If the budget is strictly below
q, exists_correct_trace_prime produces an accepted trace and proves its
output equals the intended little-endian MSM. These are conditional theorems
with concrete mathematical premises, not project axioms or a claim about
all curves. In particular, the prime-cardinality wrapper refers to the full
curve group, not an implicitly assumed prime-order subgroup.

The fixed-scalar chains use repeated complete addition as an explicit way to
enforce the constant links. Figure 4 leaves the precise implementation of
these links unspecified. This choice certifies their mathematics; it does
not claim the paper's optimized gate count or certify a particular optimized
constant-multiplication circuit. Function-valued trace arrays are only
constrained at the finite indices used by the algorithm; input base families
carry on-curve proofs and may be extended arbitrarily outside the active rows.

Tests use the smooth curve y^2=x^3+2x+2 over ZMod 17, with P=(5,1), U=3P,
w=l=1 and little-endian windows [0,1]. They verify the complete supplied
trace ending at 2P, reject substitution of P as its output, and reject a
broken initial-accumulator link even though the substitute is on the curve.
A separate nonempty zero-scalar trace verifies that final infinity is accepted.
These kernel-checked coordinate traces supplement the group-level parameter
and probability regressions; they are not production parameter instances.

## Execution plan

Baseline and milestone update: 2026-10-27. Steps 1-7 are **complete** within
the documented mathematical scope: the
library and regressions build with warnings as errors, all library theorem
axiom reports use only the standard Lean axioms, and the paper correspondence
is recorded above. Their original implementation checklist is retained below.
Step 7 includes full supplied-coordinate-trace soundness and statistical
completeness for the corrected traversal, with the Figure 3 refinement and
constant-chain choice distinguished above. Remaining scope boundaries are
listed at the end; circuit implementation and paper edits remain deferred.

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

### 5. Formalize lazy arithmetic and normalization (complete)

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

### 6. Prove the unique-zero representation (complete)

Proposed module: ShiftedEncoding.lean, after the unshifted arithmetic is stable.
Define 1 + eval B x modulo q. Under well-formedness and q <= B^n < 2*q,
prove that zero forces eval B x = q-1 and that its bounded limb vector is
unique. Establish representability and injectivity where needed.

Derive the modified multiplication identity, changed limb-wise operations
and the zero-test criterion. Recheck the quotient and residual bounds for
the extra linear terms; do not reuse the unshifted bounds without proof.
Acceptance includes boundary examples where removing the size or limb-range
condition permits a second zero representation.

### 7. Develop EC and MSM mathematics independently (complete)

The affine addition/doubling, exceptional-case and repeated-base table
substages are complete. Setup parameter selection is also checked, including
actual table witnesses. These use concrete curve groups and theorem premises,
without project axioms or additional per-step table checks.

The random-offset invariants, descending little-endian window traversal,
normalized group-level failure bound, numerical parameter rules and local
affine witness bridges are checked. Supplied coordinate traces now have
end-to-end soundness and witness composition, including lookup linkage,
initial constants and final complete subtraction. The group failure bound
has been transferred to the full coordinate witness-existence event.

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
