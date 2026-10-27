# Paper-to-Lean correspondence audit

Date: 2026-10-27. Reviewed library commit: b05a742ded781490ef2a29528bc9061bb39000ed.
The original audit added a regression in Tests/PaperAudit.lean without changing
library definitions or proofs. It was committed and pushed as a5e2004.

**Follow-up status (2026-10-27):** the subsequently authorized steps 1–4 are
complete. Native/ now proves the EC limb encodings, activation and representation
bridges, full native-trace soundness and statistical completeness.
Instances/Curve17.lean discharges all arithmetic and statistical parameters for
a small actual curve. All 281 library theorem reports use only the standard
Lean axioms (or none), and lake build passes with warnings as errors.
The findings and coverage table below describe the reviewed b05a742 baseline;
resolution notes identify changes since that audit. The printed-algorithm
mismatches and deferred implementation boundaries remain.

## Verdict

The independent Lean library covers the agreed arithmetic and coordinate-level
EC/MSM mathematics. The two numbered multiplication theorems have corresponding
soundness/completeness endpoints for the actual congruence checks. The corrected
MSM has soundness for arbitrary accepted coordinate traces and statistical
completeness under explicit numerical assumptions.

It would be inaccurate to describe this as verification of the entire paper
or of its algorithms exactly as printed. Three qualifications are essential:

1. Section 4.1's foreign-to-native EC identity encodings are not connected to
   the coordinate-level proofs.
2. The MSM proof uses descending traversal of little-endian windows; Figure 4
   prints forward traversal.
3. Complete addition uses explicitly ordered branches, not the literal
   overlapping implications of Figure 3.

No new defect in the reviewed Lean theorem statements was identified. This is
an evidence-based correspondence review, not a guarantee that no defect can
exist. The newly confirmed paper issue is an additional Figure 3 overlap with
only one infinity input; the existing ordered Lean contract already handles it.

## Sources, method, and limits

The source is the local 13-page 2025-695.pdf, SHA-256:

~~~text
c075bb9c3db566eb579495e64eb074c2783cdba34dcd1417132eb5756e7b36dd
~~~

Page numbers below are PDF page positions. The audit read the mathematical
claims, acceptance definitions, public theorem hypotheses/conclusions, relevant
proof composition, and regressions. PDF pages 4-10 were also rendered and
visually inspected to check equations, bounds, flags, and traversal order.
The performance/application sections were inventoried for scope, not benchmarked.

No supplied Lean artifact or ZIP was inspected. No new EasyCrypt source
comparison was performed in this audit; the earlier authorized consultations
remain documented in README.md. This audit does not certify the historical
release cited by Section 5, nor the Halo2 implementation.

Validation: lake build passed with warnings as errors, including the new audit
regression. All 216 library theorem dependency reports contain only standard
Lean axioms (propext, Classical.choice, Quot.sound), or no axioms. There are no
project axioms, admissions, or native_decide proofs. Lean is pinned to 4.31.0;
mathlib is pinned to fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. This uses cached
mathlib artifacts; it is not a fresh rebuild or audit of all mathlib internals.

## Findings that qualify correspondence

### F1. The native EC identity bridge was missing at the audit baseline

**Baseline type: substantial coverage gap; outside the then-agreed milestone.**

**Resolved at arithmetic-constraint level:** Native/EllipticCurve.lean encodes
(6)–(9), checks z=x^2, and proves equivalence with the coordinate predicates.
Native/Activation.lean covers native bitness and activation; Native/Trace.lean
and Native/Statistics.lean compose the gates with the entire audited trace.
Gate-port representation relations, branch selection, lookups and range
predicates remain explicit mathematical contracts, not PLONK wiring proofs.
See README.md, “Native EC identities and the full MSM trace,” for exact scope.
The following paragraphs retain the original finding.

Sections 4.1-4.2, equations (6)-(9), describe limb-level curve-membership,
slope, tangent and squared-slope identities. They require coefficient reduction,
quotient witnesses, auxiliary congruences, bounds/no-wrap conditions, and
Boolean activation. Curve membership also introduces z=x^2.

[Affine.lean](EfficientFFA/EllipticCurve/Affine.lean) starts with a genuine
field K and exact coordinate equations. Its OnCurve, AddChecks and DoubleChecks
are not the native-modulus encodings of (6)-(9). The arithmetic library proves
multiplication and normalization encodings separately. There is no theorem
that acceptance of the four implemented native EC gates implies these coordinate
predicates, or that all coordinate witnesses lift to those gate witnesses.

The coordinate trace's exact equality/copy and lookup relations likewise do
not certify a PLONK permutation/lookup implementation. Bool makes bitness true
in the mathematical type; it is not a proof of native bitness constraints.

**Impact:** arithmetic soundness plus coordinate-MSM soundness is not yet an
end-to-end theorem for a foreign-field MSM circuit. The paper already omits
some auxiliary details, so filling them would be new formalization work.

**Action:** keep the scope distinction in any paper/artifact claim. If scope is
expanded, implement and connect (6)-(9), their activation and representation
conditions. Circuit wiring remains separately deferred.

### F2. Figure 4's traversal differs from the proved algorithm

**Type: confirmed paper algorithm mismatch; corrected and documented in Lean.**

Figure 4, page 10, defines little-endian scalar windows but processes indices
from 1 to T in a double-then-add loop. Such a loop gives the first processed
window the greatest weight. The published forward traversal therefore reverses
the intended window weights when there is more than one window.

[Loop.lean](EfficientFFA/MSM/Loop.lean), loop_correct, and
[Trace.lean](EfficientFFA/MSM/Trace.lean), trace_sound_littleEndian, explicitly
use descending windows. [Tests/MSM.lean](Tests/MSM.lean) checks base-4 windows
[1,2]: the intended result is 9 times the base, while forward traversal gives
6 times the base in the small group example. The concrete coordinate trace
in [Tests/Trace.lean](Tests/Trace.lean) also uses unequal windows.

**Action:** reverse the printed loop order, or change the scalar-encoding
convention and its formula consistently. The existing Lean theorem does not
establish the printed forward algorithm's stated little-endian result.

### F3. Figure 3's overlapping implications are not complete for all allowed infinity encodings

**Type: confirmed paper completeness mismatch; ordered refinement already proved.**

Section 4.2 permits arbitrary ignored coordinates when the infinity flag is
true. Figure 3, Steps 3-4, simultaneously require R=Q when P is infinity and
R=P when Q is infinity. Section 4.4.2 explicitly expands these into coordinate
copies. If both inputs are infinity with different coordinates, no R satisfies
both copies. The existing identity_copies_iff theorem and
[Tests/EllipticCurve.lean](Tests/EllipticCurve.lean) establish this issue.

**New audit confirmation:** Section 4.4.2 defines the inverse predicate using
only x(P)=x(Q) and y(P)=-y(Q). With that literal definition, Step 5 can also
conflict with Step 3 when only P is infinity. Choose any valid finite Q and
assign the ignored coordinates of P to the coordinates of -Q. Step 3 forces
R=Q, hence a false infinity flag; Step 5 forces a true infinity flag.
[Tests/PaperAudit.lean](Tests/PaperAudit.lean),
single_infinity_literal_conflict, proves this for arbitrary finite encodings,
and instantiates valid inputs on the concrete ZMod 17 curve. The argument does
not rely on a low-order point or on both inputs being infinity. If inverse
equality was intended to include the tags, the paper must say so; that is not
the coordinate-only predicate it currently describes.

[Complete.lean](EfficientFFA/EllipticCurve/Complete.lean) already gives identity
branches precedence and restricts the inverse branch to finite inputs.
complete_sound and complete_exists prove this explicitly different contract.
The audit regression also confirms that this contract accepts the expected Q.

**Action:** specify disjoint/enabled branches and make the inverse test's
finite-input conditions explicit. Do not claim literal Figure 3 completeness
from the existing ordered-contract theorem. This finding concerns rejected
valid inputs, not an exhibited accepted incorrect sum.

## Assumptions and narrower coverage

### F4. The full coordinate probability theorem uses the full curve group, not an arbitrary prime subgroup

Sections 4 and 4.2 allow discussion of a relevant cryptographic subgroup and
mention additional subgroup-membership checks. The public statistical theorem
in [TraceStatistics.lean](EfficientFFA/MSM/TraceStatistics.lean) assumes that
Nat.card C.Point itself is prime and samples uniformly from C.Point. Its
cardinality is the number of curve points, not the coordinate-field modulus.

Generic group rejection lemmas can be useful for a subgroup, but the final
coordinate theorem is not instantiated over a subgroup embedding and does not
verify subgroup membership/cofactor clearing. Thus it cannot directly justify
the corresponding claim for a curve with composite full group order merely
because a prime-order subgroup exists.

**Action:** restrict the public theorem claim to its actual full-group scope,
or add a subgroup-to-coordinate bridge and explicit input/sampling membership
conditions if that application becomes required. This is additional scope,
not a defect in the conditional theorem.

### F5. Statistical completeness is quantitative and parameter dependent

The paper's Section 4.5 says failures are negligible without stating the full
parameter inequality. Put b=2^w and N=card(C.Point). Lean proves:

~~~text
Pr[no accepted coordinate trace for the sampled U]
  <= (1 + l*(b+1) + 2*T*l) / N
~~~

The prime-group wrapper requires w>0, l>0, in-range windows, finite on-curve
bases, prime N, and b*l+b-1<N. This numerical rule implies the required scalar
map injectivity; it is sufficient, not necessary. Existence of at least one
accepted trace is separately obtained when the numerator is strictly below N.
Calling the failure negligible requires the corresponding concrete or
asymptotic size comparison; it does not follow merely from N being prime.

The inputs/windows are fixed before sampling U. The sampler is a normalized
PMF on all curve points, including the identity; identity rejection is included
in the bound. The theorem is about witness existence, not runtime of a witness
search, nor success of an arbitrary witness generator. It is not automatically
a theorem for a sampler conditioned to exclude infinity or for a biased sampler.

At the audit baseline, the small prime-group and coordinate regressions were
separate. **Follow-up:** Instances/Curve17.lean now enumerates the actual
19-point curve group over F_17, discharges all EC gate bounds and statistical
conditions, and proves the native-trace 8/19 bound and correct-trace existence.
Production instances remain intentionally skipped; this is not a checked
SECP256k1/BLS12-381 parameter result.

### F6. Division over the paper's composite moduli needs units, not only nonzero divisors

Section 3 allows composite q. Section 3.2.2 then describes division using a
multiplication and a nonzero assertion. For a composite modulus, nonzero does
not imply an inverse or unique quotient: modulo 8, 2 has no inverse and
2*z=2 has both z=1 and z=5 as solutions.

[Division.lean](EfficientFFA/Division.lean) correctly assumes an inverse in
division_iff and encoded_division_iff. inverse_exists_iff_coprime gives the
exact unit criterion, while prime_inverse_iff discharges it from nonzeroness
only for prime modulus. [Tests/LazyNormalization.lean](Tests/LazyNormalization.lean)
contains the composite counterexamples.

The paper already qualifies the inverse-of-difference comparison in Section
3.2.3 by primality; that qualification is correct. The repository proves its
algebraic criterion and the subtraction/normalization/multiplication components,
but does not expose a single combined native disequality-gadget endpoint.
This was a composition/package gap, not a counterexample to the existing
component theorems. **Follow-up:** Native.ECEncoding.distinct_iff now supplies
a bounded-limb native polynomial endpoint for (x-y)*inverse-1 under prime q.
It does not certify a separate comparison circuit implementation.

**Action:** qualify division by invertibility, or explicitly restrict it to
prime q. Keep algebraic disequality and a complete native gadget distinct.

### F7. Constant-multiplication linkage is proved with an explicit implementation choice

Figure 4's footnote requires V and l*U to be constrained consistently with U
but leaves their exact construction unspecified. [Chains.lean](EfficientFFA/MSM/Chains.lean)
uses repeated complete-add chains, and TraceAccepts links their endpoints by
coordinate equality. The semantics are proved; no scalar-product equality is
assumed as an acceptance premise.

This construction does not certify the paper's optimized constant-multiplication
schedule, incomplete-add savings, GLV optimization, or operation counts.
Likewise, mathematically bounded function-index lookups do not certify a lookup
argument implementation. These are documented refinements/abstractions.

## Clarifications and editorial discrepancies

### F8. Order-three exclusion is unnecessary for the stated doubling equations

Section 4.3 claims the final equation needs x(P) != x(R), motivating exclusion
of order-three points. The equation instead solves linearly for y(R), without
such a division. output_determined and doubling_sound prove correctness
without that output-x premise. The accepted tangent equation itself implies
2*y(P) != 0 at a smooth finite input; no extra denominator check is introduced.

The order-three regression over ZMod 7 accepts the correct double with equal
input/output x. Order-two points are different: Figure 1's finite branch cannot
represent their infinity result. doubling_witnesses_iff precisely identifies
the nonzero-denominator condition. The paper's no-order-two assumption supplies
this completeness condition; the no-order-three restriction is unnecessarily
strong for these equations.

**Action:** simplify the explanation and retain only assumptions actually
needed for each operation. This is not a new soundness failure.

### F9. Auxiliary upper-quotient rounding is more precise in Lean

Footnote 4 (page 4) defines ignoring remainders as truncation toward zero.
For an auxiliary upper numerator Cm<0, truncation differs from floor.
The Lean definitions use lmax=floor(Cm/m), while lmin=-floor(Am/m) retains the
correct lower-end ceiling. The regression in
[Tests/Multiplication.lean](Tests/Multiplication.lean) has Cm=-60, m=100,
so the implemented lmax is -1 rather than 0.

Floor is a valid tighter upper bound. If a caller chooses wider witnesses
using the paper's truncated upper endpoint, the Lean WidthBounds condition can
still be satisfied with those supplied widths. NoWrap must be checked using
the actual widths. The two minimal-width selection procedures are not literally
identical, and there is no standalone theorem translating the paper's entire
minimal-parameter selection algorithm into the Lean structures.

**Action:** specify floor/ceiling explicitly. Do not describe this as a failed
multiplication theorem or as a missing no-wrap check.

### F10. Minor printed indexing and bound-variable errors

Theorem statements 3.1-3.2 print limb indices through n while their equations
sum through n-1; Lean uses Fin n consistently. Table 1's constant-multiplication
bound cells use output bounds z on the right-hand side, making the written
update self-referential. The intended inputs are x's bounds, as implemented by
bounded_scale, with endpoint reversal for negative constants. Figure 3's
caption also calls its complete-add routine incomplete. These are editorial
corrections; the intended mathematical statements are identifiable.

## Coverage matrix

Covered means the mathematical claim is proved under the listed explicit
conditions. Refinement means the proof addresses a documented corrected or
concretized contract. Partial means a material representation/composition
layer remains outside the endpoint.

| Paper claim | Status | Lean evidence and qualification |
|---|---|---|
| LCM reconstruction, Sections 1.2/3.1 | Covered | congruent_all_iff_lcm and eq_zero_of_congruences_of_bounds; no pairwise-coprimality assumption |
| Theorem 3.1, multiplication soundness | Covered | Multiplication.Parameters.multiplication_sound; bounded x/y/z, witness ranges, positive parameters, native/auxiliary checks, and explicit NoWrap |
| Theorem 3.2, multiplication completeness | Covered | canonical_witnesses_accept and multiplication_complete; bounded supplied correct triple, positive parameters and sufficient witness widths; no no-wrap assumption needed in this direction |
| Combined multiplication contract | Covered | accepts_iff_multiplication; modular result, not uniqueness of arbitrary bounded output representations |
| Tight residual and quotient bounds | Covered with F9 convention | Multiplication/Bounds.lean, corresponding shifted and normalization bound modules |
| Lazy operations and Table 1 | Covered | LazyArithmetic bounded_* and represents_* plus limb evaluation linearity; tracked signed values, no new operation range checks; F10 typo corrected |
| Equation (5), normalization | Covered with omitted details supplied | Normalization soundness/completeness and actual auxiliary checks; stored_normalization_* transports signed native residues; capacity required for output existence |
| Reusing multiplication moduli whenever L is approximately B^2 | Not a universal theorem | Paper describes a heuristic; Lean requires its explicit normalization WidthBounds/NoWrap rather than assuming reuse always works |
| Division/inversion | Conditional | Division unit/prime criteria and encoded_* endpoints; composite-modulus qualification in F6 |
| Inverse-of-difference disequality | Covered algebraically; partial gadget composition | prime_disequality_iff and independently proved normalization/multiplication components; F6 |
| Unique-zero representation | Covered | exists_unique_zero under q<=B^n<2q; zero_iff_native_checks additionally requires bounded limbs fitting the native interval B<=p |
| Shifted multiplication and lazy operations | Covered | ShiftedEncoding modules prove the extra linear terms, modified bounds, low-limb corrections and normalization reuse |
| EC identities (6)-(9) as native foreign-field gates | Partial | Coordinate meanings covered, native encoding/activation/limb bridge missing; F1 |
| Point witnessing and infinity convention | Covered at coordinate level | OnCurve, Valid, decode, Bool tags; auxiliary x^2 witness and native representation not composed; F1 |
| Subgroup loading/membership, Section 4.2 | Not covered end to end | Full-curve coordinate wrapper only; F4 |
| Figure 1 doubling | Covered with precise completeness condition | doubling_sound, flagged_double_witnesses_iff; no new tangent/output-x guard; F8 |
| Figure 2 incomplete addition | Covered | addition_sound/complete and incomplete_sound/complete with finite on-curve inputs and distinct x |
| Figure 3 complete addition | Refinement | CompleteAccepts with ordered branches; literal completeness fails for allowed infinity encodings; F3 |
| Internal table guards follow from equations | Covered | table_sound, table_guards and table_lookup_sound; initial guard only |
| Existence of table witnesses | Conditional and covered | table_complete, table_safe_iff_avoids, bad-offset cardinality and parameter rules; unsuitable offsets are rejected, not accepted wrong results |
| Fixed seed-to-V and seed-to-lU links | Refinement | ScaleChecks, scale_sound and full TraceAccepts endpoint linkage; F7 |
| Constant random-offset invariant | Covered | loop_invariant and row_invariant for actual group recurrence |
| Figure 4 scalar result | Covered for corrected traversal | loop_correct and trace_sound_littleEndian; F2 |
| Whole supplied coordinate trace | Covered under documented refinements | TraceAccepts contains actual coordinate equations, ranges and linkage; output and intermediate group meaning are derived |
| Statistical completeness | Conditional and covered quantitatively | uniform_littleEndian_trace_failure_bound_prime; finite prime full curve group, numerical coefficient rule and normalized sampler; F4-F5 |
| Final result may be infinity | Covered | CompleteAccepts final step and accepted nonempty zero-scalar trace in Tests/Trace.lean |
| GLV, gate/row counts, Table 2 configurations | Outside scope | No cost model or optimized implementation correspondence |
| Section 6 threshold ECDSA, self-recursion, Table 3 and benchmarks | Outside scope | No ECDSA/recursive-verifier semantics, benchmark reproduction, or Halo2/PLONK implementation proof |
| Section 5 historical EasyCrypt release claim | Not audited here | The paper says multiplication is proved and ECC formalization is ongoing; this audit concerns the independent Lean commit, not that historical artifact |

## What the endpoint assumptions really guarantee

Arithmetic acceptance contains equations modulo the native modulus and bounded
quotient witnesses. Limb ranges are explicit endpoint premises, as they are in
the numbered paper theorems. Residual bounds and auxiliary-modulus conclusions
are derived; they are not silently assumed. Allowing composite native moduli
in the algebraic theorem is a generalization of congruence mathematics, not a
claim to instantiate a finite field at a composite modulus. Noncanonical
foreign outputs are permitted; canonical equality has an explicit value-range
premise or a chosen canonical witness.

EC Curve requires a nonzero discriminant. Its points are mathlib's concrete
smooth-curve group, not an abstract group with project-supplied group-law
axioms. The public trace soundness theorem does not require a prime group or
the statistical parameter bound. Its on-curve base premise extends over the
natural-index family; only the first l bases occur in the result and contract.
Finite input families can be extended outside that range by a valid point.

TraceAccepts does not assume that supplied intermediate points are on the
curve or that the final result is an MSM. Those properties are derived from
the seed checks, constant chains, table equations, bounded lookups, loop
equations and final complete addition. The semantic relation tying a sampled
seed to its coordinate witness is stated separately in TraceWitnesses.
Completeness constructs the whole trace; it does not merely assume a trace
already exists.

The full curve statistical theorem counts failure to have any accepting trace.
Soundness applies to any accepted trace, including ones not constructed by
the canonical witness argument. These two quantifier directions are appropriate
for constraint-system soundness and statistical completeness. They should not
be advertised as a verified implementation or a proof of a random generator's
runtime behavior.

## Original recommended follow-up and current disposition

1. Use this audit to qualify the artifact/paper coverage statement immediately;
   retain the distinction between native arithmetic and coordinate-level MSM.
2. When paper edits resume, resolve F2-F3 first, then state F4-F6 assumptions,
   simplify F8 and correct F9-F10. The audit itself does not edit the paper.
3. F1 and the native disequality endpoint have now been implemented and
   composed with the whole trace. A subgroup wrapper remains a separate scope
   decision. No per-step table guards were added.
4. Keep CI, production parameter instances, circuit wiring and benchmarks out of
   the current completion claim unless explicitly brought into scope. A
   small curve cardinality/parameter instance has now been checked; it does
   not imply a production instantiation.

The known V=2P example remains an offset-rejection example, accounted for by
parameter selection and the failure budget. It is not a fresh flaw and is not
an argument for adding table checks.
