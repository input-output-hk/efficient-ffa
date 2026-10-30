# Paper results mapped to independent Lean statements

Reviewed: 2026-10-28. Library baseline: `d5e4ddc2ca4620f6aee3e566498473ba5d114645`.
This is the current correspondence map, including native EC encodings and
prime-order subgroup support. [PAPER_AUDIT.md](PAPER_AUDIT.md) preserves the
earlier audit and its findings; its original coverage table describes an older baseline.

## Scope and interpretation

The local 13-page paper, *Efficient Foreign-Field Arithmetic in PLONK*
(ePrint 2025/695), has **two numbered result statements: Theorems 3.1 and 3.2**.
There are no other numbered lemmas, propositions, corollaries or claims.
Most of the work is stated through equations, figure contracts and prose.
This inventory assigns stable IDs to those mathematical claim families and
also records the implementation, performance and application claims that have
no Lean counterpart. Repeated claims are grouped; cited background is grouped
separately rather than treated as a new theorem of this paper.

Source PDF SHA-256:

~~~text
c075bb9c3db566eb579495e64eb074c2783cdba34dcd1417132eb5756e7b36dd
~~~

Page numbers are PDF page positions. The inventory uses extracted text and
visual review of mathematical pages 4–10. Only this paper, the independent
library and its existing documentation/regressions were consulted for this
mapping. No supplied Lean repository/archive was opened, and no new EasyCrypt
comparison was performed.

A link below identifies an **existing declaration**, not a proposed proof.
Definitions are included where needed to identify the acceptance predicate or
algorithm being proved; they are not themselves counted as proofs of a claim.
The source links expose the theorem's exact binders and hypotheses.
[Tests/PaperCorrespondence.lean](Tests/PaperCorrespondence.lean) checks all
referenced declaration names, with row IDs in comments. It does not automate
semantic comparison of prose with theorem statements. That comparison and the
completeness of this inventory are manual review judgments.

| Status | Meaning |
|---|---|
| Covered | A theorem or collection of theorems establishes the stated mathematical result under its explicit assumptions. It does not certify a PLONK implementation. |
| Conditional | A corresponding theorem exists, but a material domain or parameter condition must be made explicit when restating the paper claim. |
| Refined | Lean proves a corrected/different formulation, or a counterexample explains why the literal formulation is unsuitable. This is not proof of the printed statement. |
| Partial | There is a related formal result, but it does not establish the entire claim. |
| Unmapped | No corresponding formal statement/proof was identified in this library. |
| Background | A cited foundation or contextual assertion outside the library's subject. |

The 89 rows are inventory units, not a theorem count or a percentage of
verification. Several rows can share a theorem and one row can require many
lemmas. The library's 319-theorem count is a separate implementation metric.

## Headline theorem contracts

**Theorem 3.1 (M10).** For a multiplication parameter bundle P, positive moduli
and radix, the four no-wrap conditions, bounded x/y/z limbs, and
`P.Accepts x y z u v` imply
`eval P.B x * eval P.B y ≡ eval P.B z [ZMOD P.q]`.
Acceptance includes quotient ranges and the native/auxiliary congruences.
Limb well-formedness is supplied separately. This is
[M.multiplication_sound](EfficientFFA/Multiplication/Soundness.lean#L16).

**Theorem 3.2 (M11).** Positivity, sufficient quotient widths, bounded x/y/z
limbs and the same modular product relation imply
`∃ u v, P.Accepts x y z u v`. This is
[M.multiplication_complete](EfficientFFA/Multiplication/Completeness.lean#L53).
The proof does not need no-wrap assumptions in this direction. Conversely,
soundness does not need width sufficiency. Minimal limb counts/bit widths and
primality of p are unnecessary for these integer-congruence theorems; the
paper's field-based implementation has additional representation obligations.
The rounding refinement in M04 must be retained when comparing parameter definitions.

**EC/MSM soundness (O04, T08, T10).** For a valid native EC encoding and valid
finite bases, every accepted full native trace has a valid output equal to
`Σ j, (Σ i, (2^w)^i * windows i j) • base j`.
The endpoint is [E.trace_sound_littleEndian](EfficientFFA/Native/Trace.lean#L157).
It uses the ordered complete-add contract and descending traversal of
little-endian windows. It does not prove Figures 3 and 4 literally as printed.
No additional per-entry table guard is introduced: accepted table equations
imply the internal guards (T02). Table witness existence is a separate
parameter/seed-selection result (T03–T04).

**Statistical completeness (T11–T14).** Put b=2^w, use l bases and t windows,
and sample U uniformly from a group of prime order N. With w,l>0,
`b*l+b−1 < N`, valid fixed bases and windows in [0,b), native witness
failure has probability at most

~~~text
(1 + l*(b+1) + 2*t*l) / N.
~~~

This is [E.uniform_littleEndian_failure_bound](EfficientFFA/Native/Statistics.lean#L21), or
[E.uniform_subgroup_failure_bound](EfficientFFA/Native/Subgroup.lean#L38) when sampling inside a prime-order
subgroup H with N=card H. The numerator includes both setup and loop failures.
It is an explicit finite bound, not an unconditional asymptotic negligibility
theorem. Witness existence follows when the budget is below N. Native checked
subgroup loading additionally uses the coprime-cofactor condition (E11).

## Reference notation

Each short prefix in a declaration link expands as follows; these aliases are
for this document, not new Lean namespaces. The checked reference index uses
fully qualified names. E is the namespace for the parameterized ECEncoding
contract, not a claim that every numerical choice supplies such an encoding.

| Prefix | Lean namespace |
|---|---|
| A | `EfficientFFA` |
| M | `EfficientFFA.Multiplication.Parameters` |
| MB | `EfficientFFA.Multiplication` |
| L | `EfficientFFA.LazyArithmetic` |
| N | `EfficientFFA.Normalization.Parameters` |
| NB | `EfficientFFA.Normalization` |
| D | `EfficientFFA.Division` |
| S | `EfficientFFA.ShiftedEncoding` |
| SM | `EfficientFFA.ShiftedEncoding.Multiplication.Parameters` |
| SMB | `EfficientFFA.ShiftedEncoding.Multiplication` |
| EC | `EfficientFFA.EllipticCurve` |
| C | `EfficientFFA.EllipticCurve.Curve` |
| MSM | `EfficientFFA.MSM` |
| P | `EfficientFFA.Native.Polynomial` |
| G | `EfficientFFA.Native.Parameters` |
| X | `EfficientFFA.Native.Expression` |
| E | `EfficientFFA.Native.ECEncoding` |
| Native | `EfficientFFA.Native` |
| SG | `EfficientFFA.Subgroup` |
| Audit | `EfficientFFA.Tests.PaperAudit` |

## Numbered-object index

| Paper object | Inventory rows |
|---|---|
| Theorems 3.1, 3.2 | M10, M11 |
| Equations (1), (2), (3), (4) | M02; M05–M06; M07; M08 |
| Equation (5) | L07–L10 |
| Equations (6), (7), (8), (9) | E02; E03; E04; E05 |
| Table 1 | L01–L05 |
| Figure 1 | O01–O02 |
| Figure 2 | O03 |
| Figure 3 | O04–O06; O07 for cost claims |
| Figure 4 | T01–T14, T16 |
| Table 2 | P01–P05 |
| Figure 5 | P08 |
| Table 3 | P11; P09–P10 for its application/parameters |

## Claim inventory

### Foundations and representation

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **F01** — §1.2, p.2 | Simultaneous modular equalities combine modulo the LCM. | Covered | [A.moduliLCM](EfficientFFA/Arithmetic.lean#L14), [A.congruent_all_iff_lcm](EfficientFFA/Arithmetic.lean#L19). No pairwise-coprimality assumption is needed. This is the LCM form of the CRT argument, not reconstruction of arbitrary unrelated residues. |
| **F02** — §1.2, p.2; §3.1, pp.4–5 | A bounded integer divisible by all selected moduli must be zero. | Covered | [A.eq_zero_of_congruences_of_bounds](EfficientFFA/Arithmetic.lean#L43), [A.eq_zero_of_modEq_of_bounds](EfficientFFA/Arithmetic.lean#L29). Strict signed bounds relative to the positive LCM are essential. |
| **F03** — §3, p.4 | Little-endian limb representation and capacity B^n ≥ q. | Covered | [A.eval](EfficientFFA/Limbs.lean#L16), [A.WellFormed](EfficientFFA/Limbs.lean#L20), [A.exists_limbs](EfficientFFA/Representation.lean#L7), [A.exists_canonical_limbs](EfficientFFA/Representation.lean#L41), [A.eval_bounds](EfficientFFA/Representation.lean#L59). Existence requires capacity and a valid base. Lean does not require n to be the smallest possible length. |
| **F04** — §3, p.4; §3.2.3, p.6 | Bounded integer representations are unique; residue representations can be noncanonical. | Partial | [A.eval_injective](EfficientFFA/Representation.lean#L70), [M.canonical_output](EfficientFFA/Multiplication.lean#L17). Injectivity is for integer evaluation, not reduction modulo q. Noncanonical multiplication examples are in Tests/Multiplication.lean; no general named theorem classifies all duplicate residue encodings. Canonical output needs an explicit [0,q) bound. |
| **F05** — §3, p.4 | Limbs fit natively for suitable B; sufficient headroom is needed for computation. | Partial | [L.lift_unique](EfficientFFA/LazyArithmetic.lean#L88), [M.NoWrap](EfficientFFA/Multiplication/Definitions.lean#L80). The library proves explicit interval/no-wrap conditions. The prose heuristic B ≪ √p and the resulting suggested minimum limb count are not necessity or optimization theorems. |

### Multiplication: §§3.1–3.1.3

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **M01** — §3.1, p.4, before (1) | Expand a product of limb evaluations. | Covered | [A.eval_mul](EfficientFFA/Limbs.lean#L29). Exact integer identity. |
| **M02** — §3.1, p.4, (1) | Reduce coefficients modulo q and introduce an integer quotient k. | Covered | [A.mulResidual_mod](EfficientFFA/Limbs.lean#L42), [A.mulResidual_dvd_iff](EfficientFFA/Limbs.lean#L49), [A.multiplication_iff_quotient](EfficientFFA/Limbs.lean#L54). Equivalence is with modular multiplication, not integer equality of the original operands. |
| **M03** — §1.2, p.3; §3.1, p.4 | Weighted coefficient sums give the displayed tighter lower and upper bounds. | Covered | [MB.weighted_sum_bounds](EfficientFFA/Multiplication/Bounds.lean#L7), [MB.weighted_product_bounds](EfficientFFA/Multiplication/Bounds.lean#L22), [M.residual_bounds](EfficientFFA/Multiplication/Bounds.lean#L57). Bounds use actual reduced coefficients and bounded limbs. No theorem claims a strict improvement for every parameter choice or a smaller circuit for every input. |
| **M04** — §3.1, p.4; footnote 4; §3.1.1, p.5 | Derive k and auxiliary quotient intervals by rounding. | Refined | [MB.quotient_interval](EfficientFFA/Multiplication/Bounds.lean#L49), [M.kmin](EfficientFFA/Multiplication/Definitions.lean#L31), [M.kmax](EfficientFFA/Multiplication/Definitions.lean#L32), [M.lmin](EfficientFFA/Multiplication/Definitions.lean#L44), [M.lmax](EfficientFFA/Multiplication/Definitions.lean#L45). Negative lower endpoints use the ceiling convention. Lean floors the auxiliary upper quotient even when its numerator is negative; footnote 4 prescribes truncation toward zero. Lean’s upper bound is then tighter and remains valid. The resulting range widths and no-wrap inequalities must be checked together. |
| **M05** — §3.1, pp.4–5, (2) | Shift k to u and range-check it in a power-of-two interval. | Covered | [M.nativeResidual](EfficientFFA/Multiplication/Definitions.lean#L47), [M.Umax](EfficientFFA/Multiplication/Definitions.lean#L33), [M.WidthBounds](EfficientFFA/Multiplication/Definitions.lean#L76), [M.Accepts](EfficientFFA/Multiplication/Definitions.lean#L93). Widths need only be sufficient, not minimal. Increasing them requires rechecking NoWrap; choosing too small a width can lose completeness. |
| **M06** — §3.1, p.4, after (2) | Native and auxiliary congruences plus the LCM bounds reconstruct the integer equation. | Covered | [M.nativeResidual_bounds](EfficientFFA/Multiplication/Bounds.lean#L88), [M.NoWrap](EfficientFFA/Multiplication/Definitions.lean#L80), [M.multiplication_sound](EfficientFFA/Multiplication/Soundness.lean#L16). The native p check and every auxiliary check are part of acceptance. |
| **M07** — §3.1.1, pp.4–5, (3) | Reduce coefficients again modulo m and introduce the shifted auxiliary quotient. | Covered | [M.auxCore](EfficientFFA/Multiplication/Definitions.lean#L51), [M.auxResidual](EfficientFFA/Multiplication/Definitions.lean#L56), [M.auxCore_congr](EfficientFFA/Multiplication/Soundness.lean#L8), [M.auxCore_bounds](EfficientFFA/Multiplication/Bounds.lean#L71). The constant (kmin*q) mod m is reduced as a whole; auxiliary quotient ranges are explicit. |
| **M08** — §3.1.1, p.5, (4) | The two auxiliary residual bounds prevent wraparound modulo p. | Covered | [M.auxResidual_bounds](EfficientFFA/Multiplication/Bounds.lean#L98), [M.NoWrap](EfficientFFA/Multiplication/Definitions.lean#L80). Strict bounds are checked for each auxiliary modulus. |
| **M09** — §3.1.2, p.5 | Combined multiplication gate: native identities, quotient ranges, bounded output. | Covered | [M.Accepts](EfficientFFA/Multiplication/Definitions.lean#L93), [M.accepts_iff_multiplication](EfficientFFA/Multiplication.lean#L7). WellFormed assumptions on x,y,z are separate from Accepts. No PLONK lookup or range-check implementation is verified. |
| **M10** — Theorem 3.1, p.5 | Every accepting bounded triple represents multiplication modulo q. | Covered | [M.multiplication_sound](EfficientFFA/Multiplication/Soundness.lean#L16). Requires Positive and NoWrap plus bounded x,y,z and acceptance. WidthBounds and representational capacity are unnecessary for this direction once the triple is supplied. |
| **M11** — Theorem 3.2, p.6 | Every correct bounded multiplication triple admits accepting quotient witnesses. | Covered | [M.canonical_witnesses_accept](EfficientFFA/Multiplication/Completeness.lean#L16), [M.multiplication_complete](EfficientFFA/Multiplication/Completeness.lean#L53). Requires Positive and WidthBounds plus bounded x,y,z and modular multiplication. NoWrap is unnecessary for witness existence. This supplies witnesses for a given z, not a proof that every residue has a bounded representation without capacity. |

### Lazy arithmetic and normalization: §3.2

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **L01** — §3.2, p.6; Table 1, p.7, addition | Limb-wise addition preserves the represented value and adds limb bounds. | Covered | [A.eval_add](EfficientFFA/Limbs.lean#L72), [L.bounded_add](EfficientFFA/LazyArithmetic.lean#L14), [L.represents_add](EfficientFFA/LazyArithmetic.lean#L56). Tracked integer lifts justify native arithmetic without inserting a fresh range check after each addition. |
| **L02** — §3.2, p.6; Table 1, p.7, subtraction | Limb-wise subtraction works with signed lifts, including native wraparound. | Covered | [A.eval_sub](EfficientFFA/Limbs.lean#L76), [L.bounded_sub](EfficientFFA/LazyArithmetic.lean#L22), [L.represents_sub](EfficientFFA/LazyArithmetic.lean#L62). The lower endpoint subtracts the other upper endpoint, and conversely. Stored residues must represent the tracked lifts. |
| **L03** — Table 1, p.7, negation | Negation reverses and negates interval endpoints. | Covered | [L.eval_neg](EfficientFFA/LazyArithmetic.lean#L83), [L.bounded_neg](EfficientFFA/LazyArithmetic.lean#L30), [L.represents_neg](EfficientFFA/LazyArithmetic.lean#L68). Uses signed integer lifts. |
| **L04** — §3.2.2, p.6; Table 1, p.7, constant addition | Add a constant limb-wise and update bounds. | Covered | [L.bounded_add_constant](EfficientFFA/LazyArithmetic.lean#L36), [L.represents_add_constant](EfficientFFA/LazyArithmetic.lean#L73). The constant is supplied with its limb values. |
| **L05** — §3.2.2, p.6; Table 1, p.7, constant multiplication | Scale limbs, swapping bound endpoints for a negative constant. | Refined | [A.eval_scale](EfficientFFA/Limbs.lean#L80), [L.bounded_scale](EfficientFFA/LazyArithmetic.lean#L41), [L.represents_scale](EfficientFFA/LazyArithmetic.lean#L78). The printed bound row refers to output z where it needs input x bounds. Lean states the rule using the input bounds and handles either sign. |
| **L06** — §3.2, p.6; §3.2.1, footnote 5 | Compose lazy operations while keeping bounds inside the normalization limit. | Covered | [L.represents_reduced](EfficientFFA/LazyArithmetic.lean#L51), [N.stored_normalization_sound](EfficientFFA/Normalization.lean#L52), [N.stored_normalization_exists](EfficientFFA/Normalization.lean#L59), [N.subtraction_normalization_sound](EfficientFFA/Normalization.lean#L67). Soundness uses a bounded lift, not small unsigned stored residues. Exceeding the stated limit leaves this theorem’s domain; it is not an impossibility theorem for every normalization scheme. |
| **L07** — §3.2.1, p.6, (5) | Coefficient-reduced linear equality characterizes normalization. | Covered | [NB.residual_mod](EfficientFFA/Normalization/Definitions.lean#L14), [NB.residual_dvd_iff](EfficientFFA/Normalization/Definitions.lean#L18), [NB.normalization_iff_quotient](EfficientFFA/Normalization/Definitions.lean#L23). Normalization preserves the foreign residue. |
| **L08** — §3.2.1, p.6, bounds after (5) | Bound the normalization residual from signed input bounds. | Covered | [NB.weighted_linear_bounds](EfficientFFA/Normalization/Bounds.lean#L7), [N.residual_bounds](EfficientFFA/Normalization/Bounds.lean#L25). Includes the displayed conservative lower bound using limit+B. |
| **L09** — §3.2.1, p.6, “proceed as in Section 3.1” | Native/auxiliary normalization checks are sound and complete. | Covered | [N.auxCore_congr](EfficientFFA/Normalization/Soundness.lean#L8), [N.auxCore_bounds](EfficientFFA/Normalization/Bounds.lean#L32), [N.nativeResidual_bounds](EfficientFFA/Normalization/Bounds.lean#L44), [N.auxResidual_bounds](EfficientFFA/Normalization/Bounds.lean#L54), [N.normalization_sound](EfficientFFA/Normalization/Soundness.lean#L16), [N.normalization_complete](EfficientFFA/Normalization/Completeness.lean#L54), [N.accepts_iff_normalization](EfficientFFA/Normalization.lean#L8). Lean fills in the omitted auxiliary construction with explicit positivity, width, no-wrap and limb-bound hypotheses. |
| **L10** — §3.2.1, p.6 | A bounded lazy input can be normalized to a well-formed output. | Covered | [N.normalization_exists](EfficientFFA/Normalization.lean#L17), [N.stored_normalization_exists](EfficientFFA/Normalization.lean#L59). Output existence requires q ≤ B^n in addition to valid normalization parameters. Native stored-residue transport is included. |
| **L11** — §3.2.1–3.2.2, p.6 | L around B² permits many additions; multiplication moduli can often be reused; small constants are cheap. | Unmapped | **No direct counterpart.** These are parameter/performance heuristics. No theorem guarantees reuse for every L<B², exactly B safe additions from arbitrary starting bounds, or a universal optimal constant threshold. Explicit bound rules and parameter conditions remain available. |

### Division and comparison: §§3.2.2–3.2.3

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **D01** — §3.2.2, p.6 | Division is multiplication plus a nonzero condition; inversion is division of one. | Conditional | [D.inverse_exists_iff_coprime](EfficientFFA/Division.lean#L7), [D.division_iff](EfficientFFA/Division.lean#L18), [D.encoded_division_iff](EfficientFFA/Division.lean#L61), [D.encoded_inverse_iff](EfficientFFA/Division.lean#L69). For general q, the divisor must be a unit (coprime to q). Nonzero alone suffices only over a field. Section 3 allows composite q, so this qualification matters. |
| **D02** — §3.2.3, p.6 | For prime q, an inverse of the difference exists iff the two residues differ. | Covered | [D.prime_inverse_iff](EfficientFFA/Division.lean#L34), [D.prime_disequality_iff](EfficientFFA/Division.lean#L55), [E.distinct_iff](EfficientFFA/Native/EllipticCurve.lean#L71). This is disequality, not an ordering comparison. Native EC disequality uses a combined inverse identity; the particular subtraction–normalization–multiplication circuit layout is not compiled. |

### Unique-zero encoding: §3.2.4

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **Z01** — §3.2.4, pp.6–7 | When q ≤ B^n < 2q, shifted value 1+eval has a unique bounded zero encoding. | Covered | [S.value](EfficientFFA/ShiftedEncoding/Representation.lean#L6), [S.zero_iff_eval](EfficientFFA/ShiftedEncoding/Representation.lean#L9), [S.exists_unique_zero](EfficientFFA/ShiftedEncoding/Representation.lean#L27), [S.zero_iff_limbs](EfficientFFA/ShiftedEncoding/Representation.lean#L38). Zero is exactly the bounded limb representation of q−1; the capacity and strict upper bound are essential. |
| **Z02** — §3.2.4, p.7 | The shifted encoding still represents every foreign residue. | Covered | [S.exists_representation](EfficientFFA/ShiftedEncoding/Representation.lean#L51). Requires representational capacity and valid radix assumptions. |
| **Z03** — §3.2.4, p.7 | Zero testing reduces to checking the individual limbs against q−1. | Covered | [S.zero_iff_native_checks](EfficientFFA/ShiftedEncoding/Representation.lean#L63). In addition to q ≤ B^n < 2q, native equality needs B ≤ p to prevent limb aliasing. Cheapness in rows/copy constraints is not proved. |
| **Z04** — §3.2.4, p.7, displayed multiplication identity | Shifted multiplication introduces the additional linear terms. | Covered | [SMB.shifted_product_identity](EfficientFFA/ShiftedEncoding/Multiplication/Definitions.lean#L16), [SMB.residual_mod](EfficientFFA/ShiftedEncoding/Multiplication/Definitions.lean#L22), [SMB.multiplication_iff_quotient](EfficientFFA/ShiftedEncoding/Multiplication/Definitions.lean#L32), [SM.residual_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L9), [SM.auxCore_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L25), [SM.nativeResidual_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L44), [SM.auxResidual_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L54). Revised bounds and quotient parameters are used, not the unshifted bounds without adjustment. |
| **Z05** — §3.2.4, p.7, “extends in a natural way” | The adapted shifted multiplication checks are sound and complete. | Covered | [SM.auxCore_congr](EfficientFFA/ShiftedEncoding/Multiplication/Soundness.lean#L8), [SM.multiplication_sound](EfficientFFA/ShiftedEncoding/Multiplication/Soundness.lean#L16), [SM.multiplication_complete](EfficientFFA/ShiftedEncoding/Multiplication/Completeness.lean#L54), [SM.accepts_iff_multiplication](EfficientFFA/ShiftedEncoding/Multiplication.lean#L7), [SM.multiplication_exists](EfficientFFA/ShiftedEncoding/Multiplication.lean#L17). Output existence additionally uses capacity; acceptance of a supplied triple uses its explicit bounds and shifted parameter conditions. |
| **Z06** — §3.2.4, p.7 | Normalization is unchanged because the two shifts cancel. | Covered | [S.value_congr_iff](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L112), [S.normalization_iff](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L116), [S.stored_normalization_sound](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L122), [S.stored_normalization_exists](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L131). The unshifted normalization checks preserve the shifted residue too. |
| **Z07** — §3.2.4, p.7 | Adjust the least significant limb for shifted linear operations. | Covered | [S.eval_bump](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L16), [S.value_add](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L21), [S.value_sub](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L26), [S.value_neg](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L31), [S.value_add_constant](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L36), [S.value_scale](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L41), [S.bounded_add](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L56), [S.bounded_sub](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L61), [S.bounded_neg](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L66), [S.bounded_scale](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L70). Addition uses +1, subtraction −1, negation −2, scaling +(c−1); corresponding signed bounds and native-representation lemmas are available. Nonempty limb vectors are needed for a low-limb correction. |

### EC equations and native encoding: §§4–4.2

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **E01** — §4, p.7 | Affine coordinates on a smooth short-Weierstrass curve describe actual elliptic-curve points. | Covered | [EC.Curve](EfficientFFA/EllipticCurve/Affine.lean#L10), [C.equation_iff](EfficientFFA/EllipticCurve/Affine.lean#L28), [C.nonsingular](EfficientFFA/EllipticCurve/Affine.lean#L31), [C.point](EfficientFFA/EllipticCurve/Affine.lean#L35), [C.point_ne_zero](EfficientFFA/EllipticCurve/Affine.lean#L38), [C.point_injective](EfficientFFA/EllipticCurve/Affine.lean#L41). The abstract field and smooth curve are explicit. Group semantics come from mathlib, rather than an assumed group law for arbitrary coordinates. |
| **E02** — §4.1, p.7, (6) | Membership uses a quadratic identity with an intermediate z=x². | Covered | [Native.GateKind.expression](EfficientFFA/Native/EllipticCurve.lean#L15), [E.onCurve_iff](EfficientFFA/Native/EllipticCurve.lean#L91). The native predicate checks both the square relation and the curve equation. An unlinked z is insufficient. |
| **E03** — §4.1.2, p.8, (7) | The signed chord slope identities encode the line through P and ±Q. | Covered | [EC.chord](EfficientFFA/EllipticCurve/Affine.lean#L61), [EC.AddChecks](EfficientFFA/EllipticCurve/Affine.lean#L65), [EC.add_checks_iff](EfficientFFA/EllipticCurve/Affine.lean#L87), [E.add_iff](EfficientFFA/Native/EllipticCurve.lean#L108). The addition contract uses the appropriate signed equation. Identification with group addition requires valid inputs and distinct x-coordinates, unless that distinction is derived by a surrounding invariant. |
| **E04** — §4.1.3, p.8, (8) | The tangent equation defines doubling. | Conditional | [EC.tangent](EfficientFFA/EllipticCurve/Affine.lean#L62), [EC.DoubleChecks](EfficientFFA/EllipticCurve/Affine.lean#L70), [EC.double_checks_iff](EfficientFFA/EllipticCurve/Affine.lean#L103), [C.double_den_ne](EfficientFFA/EllipticCurve/GroupLaw.lean#L76), [E.double_iff](EfficientFFA/Native/EllipticCurve.lean#L123). Completeness for a finite affine result requires 2*y(P) ≠ 0. Soundness of accepted checks derives the needed nonzero denominator from smoothness. |
| **E05** — §4.1.4, p.8, (9), plus (7) with Q=R | The slope fixes x(R), and the linear relation fixes y(R). | Covered | [EC.result](EfficientFFA/EllipticCurve/Affine.lean#L58), [EC.output_determined](EfficientFFA/EllipticCurve/Affine.lean#L77), [C.result_group](EfficientFFA/EllipticCurve/GroupLaw.lean#L42), [C.addition_sound](EfficientFFA/EllipticCurve/GroupLaw.lean#L58), [C.doubling_sound](EfficientFFA/EllipticCurve/GroupLaw.lean#L87). No division by x(R)−x(P) is needed to determine y(R). The coordinate checks are connected to actual group addition. |
| **E06** — §4.1, pp.7–8 | Encode the foreign identities over the native modulus using coefficient reduction and bounds. | Covered | [P.reduce_congr](EfficientFFA/Native/Polynomial.lean#L76), [P.eval_bounds](EfficientFFA/Native/Polynomial.lean#L103), [G.residual_congr](EfficientFFA/Native/Gate.lean#L69), [G.residual_bounds](EfficientFFA/Native/Gate.lean#L72), [G.auxCore_bounds](EfficientFFA/Native/Gate.lean#L76), [G.auxCore_congr](EfficientFFA/Native/Gate.lean#L86), [G.sound](EfficientFFA/Native/Gate.lean#L95), [G.accepts_iff](EfficientFFA/Native/Gate.lean#L177), [X.compile_eval](EfficientFFA/Native/Expression.lean#L57), [X.checks_iff](EfficientFFA/Native/Expression.lean#L107), [E.check_iff](EfficientFFA/Native/EllipticCurve.lean#L54). The sparse-polynomial/limb compiler is proved correct. Each gate kind requires valid arithmetic parameters, foreign modulus agreement, capacity and well-formed represented inputs. |
| **E07** — §4.1, p.7 | Replacing x³ by x*z reduces limb-product complexity from cubic to quadratic. | Partial | [Native.GateKind.expression](EfficientFFA/Native/EllipticCurve.lean#L15), [X.compile_eval](EfficientFFA/Native/Expression.lean#L57). The linked quadratic templates are formalized. There is no separate asymptotic degree, monomial-count, row-count or cost theorem. |
| **E08** — §4.1, p.8 | Boolean activation disables an identity at zero and enforces it at one. | Covered | [Native.bit_cases](EfficientFFA/Native/Activation.lean#L7), [G.Activated](EfficientFFA/Native/Activation.lean#L26), [G.activated_sound](EfficientFFA/Native/Activation.lean#L34), [G.activated_one](EfficientFFA/Native/Activation.lean#L46), [G.activated_zero](EfficientFFA/Native/Activation.lean#L51). The bit-root argument needs the native prime/field assumption; composite native rings can have extra idempotents. Activated gate arithmetic is proved, but E.Check selects activation one and branch dispatch remains a logical predicate. |
| **E09** — §4.1, p.7 | The same EC-identity approach can be adapted to the unique-zero representation. | Unmapped | **No direct counterpart.** Shifted arithmetic is proved separately. Native EC gates and traces currently use ordinary, unshifted limbs; no shifted EC encoding/trace bridge is present. |
| **E10** — §4.2, p.8 | An infinity flag permits arbitrary coordinates for infinity; finite coordinates must be on the curve. | Covered | [EC.Encoded](EfficientFFA/EllipticCurve/Flagged.lean#L6), [C.Valid](EfficientFFA/EllipticCurve/Flagged.lean#L14), [C.decode](EfficientFFA/EllipticCurve/Flagged.lean#L16), [C.decode_finite](EfficientFFA/EllipticCurve/Flagged.lean#L19), [C.decode_infinity](EfficientFFA/EllipticCurve/Flagged.lean#L22), [E.flag_iff](EfficientFFA/Native/Trace.lean#L15). Lean Boolean tags have a native bit check. There is no standalone compiled implementation of the paper’s unified Valid gate or proof of its 2n+1-cell cost. Finite membership and tagged semantics are connected in the operation/trace contracts. |
| **E11** — §4.2, p.8 | Check loaded points for subgroup membership, then preserve subgroup membership under operations. | Conditional | [SG.mem_iff_card_nsmul_eq_zero](EfficientFFA/EllipticCurve/Subgroup.lean#L8), [E.member_iff](EfficientFFA/Native/Subgroup.lean#L24), [C.trace_output_mem_subgroup](EfficientFFA/MSM/Subgroup.lean#L36), [E.trace_output_mem_subgroup](EfficientFFA/Native/Subgroup.lean#L12). The native membership predicate checks on-curve and [card H]P=0 via a complete-addition chain. Equivalence to membership in the chosen H requires coprimality of card H with the quotient order. Output closure needs subgroup inputs; prime subgroup order alone does not identify a subgroup when the cofactor shares that prime. |
| **E12** — §4, p.7, naïve point-addition operation count | Dedicated identities avoid the cost of composing generic foreign-field operations. | Partial | [E.add_iff](EfficientFFA/Native/EllipticCurve.lean#L108), [E.double_iff](EfficientFFA/Native/EllipticCurve.lean#L123). Correctness of the dedicated identities is proved. The stated naïve counts (including five subtractions, five normalizations and three multiplications) and comparative savings have no formal operation-cost theorem. |

### EC operations: §§4.3–4.4

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **O01** — §4.3, p.8, Figure 1 | Doubling preserves the infinity flag and uses tangent/addition equations in the finite branch. | Conditional | [C.DoubleAccepts](EfficientFFA/EllipticCurve/Flagged.lean#L26), [C.flagged_double_sound](EfficientFFA/EllipticCurve/Flagged.lean#L35), [C.flagged_double_complete](EfficientFFA/EllipticCurve/Flagged.lean#L46), [C.flagged_double_witnesses_iff](EfficientFFA/EllipticCurve/Flagged.lean#L55), [C.flagged_double_complete_of_no_two_torsion](EfficientFFA/EllipticCurve/Flagged.lean#L91). Sound for accepted checks. Complete when the finite tangent denominator is nonzero; no nontrivial two-torsion is a sufficient group-level condition, consistent with the paper’s restriction. |
| **O02** — §4.3, p.8, explanation of x(2P) ≠ x(P) | Excluding order three is used to justify the displayed doubling method. | Refined | [EC.output_determined](EfficientFFA/EllipticCurve/Affine.lean#L77), [C.flagged_double_witnesses_iff](EfficientFFA/EllipticCurve/Flagged.lean#L55). Lean does not need x(2P) ≠ x(P) or an order-three exclusion. The y-output is determined without dividing by that difference. The order-three regression in Tests/EllipticCurve.lean demonstrates this stronger coverage. |
| **O03** — §4.4.1, p.9, Figure 2 | Incomplete addition is sound and complete for valid finite inputs with distinct x. | Covered | [C.IncompleteAccepts](EfficientFFA/EllipticCurve/Flagged.lean#L30), [C.incomplete_sound](EfficientFFA/EllipticCurve/Flagged.lean#L62), [C.incomplete_complete](EfficientFFA/EllipticCurve/Flagged.lean#L70), [C.addition_sound](EfficientFFA/EllipticCurve/GroupLaw.lean#L58), [C.addition_complete](EfficientFFA/EllipticCurve/GroupLaw.lean#L65). The finite result and its curve membership are derived. Whether input validity/distinctness is separately checked or inherited is a surrounding-contract question. |
| **O04** — §4.4.2, p.9, Figure 3 | Complete addition handles identities, inverses, doubling and distinct inputs. | Refined | [C.CompleteAccepts](EfficientFFA/EllipticCurve/Complete.lean#L9), [C.complete_sound](EfficientFFA/EllipticCurve/Complete.lean#L21), [C.complete_exists](EfficientFFA/EllipticCurve/Complete.lean#L48), [C.complete_correct](EfficientFFA/EllipticCurve/Complete.lean#L76), [E.complete_iff](EfficientFFA/Native/Trace.lean#L47). Lean uses ordered branches. It proves complete addition, but not the literal conjunction of overlapping implications printed in Figure 3. It also handles order-two inputs by the inverse branch. |
| **O05** — §4.2; Figure 3 Steps 3–4, p.9 | Copy the other input for an infinity input. | Refined | [EC.IdentityCopies](EfficientFFA/EllipticCurve/Flagged.lean#L104), [EC.identity_copies_iff](EfficientFFA/EllipticCurve/Flagged.lean#L108), [E.copy_iff](EfficientFFA/Native/EllipticCurve.lean#L82), [E.encodedCopy_iff](EfficientFFA/Native/Trace.lean#L22). The two literal copy implications require identical encodings when both inputs are infinity, which conflicts with arbitrary infinity coordinates. Ordered dispatch resolves this. Native copy predicates express equality of represented field values; literal equality of every limb of noncanonical encodings is a stronger contract. |
| **O06** — §4.4.2; Figure 3 Steps 3 and 5, p.9 | Coordinate-only inverse detection coexists with infinity-copy branches. | Refined | [Audit.single_infinity_literal_conflict](Tests/PaperAudit.lean#L10), [C.CompleteAccepts](EfficientFFA/EllipticCurve/Complete.lean#L9). The audit theorem refutes the literal simultaneous obligations when one input is infinity with coordinates −Q. Lean’s ordered branches resolve the overlap. Figure 3’s “incomplete” caption is also inconsistent with its surrounding complete-addition discussion. |
| **O07** — §4.4, p.9; Figure 3 | Copying is free and unique-zero comparison makes complete addition cheap. | Unmapped | **No direct counterpart.** No row/copy/lookup cost model or full selector/copy-constraint compiler is present. Semantic equalities do not establish these resource claims. |

### MSM tables, loop and probability: §4.5

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **T01** — §4.5, pp.9–10; Figure 4 Steps 3–4, p.10 | Initialize offset tables so entry k represents kP−V, V=(b−1)U. | Covered | [MSM.entry](EfficientFFA/MSM/Tables.lean#L6), [MSM.entry_succ](EfficientFFA/MSM/Tables.lean#L8), [C.table_sound](EfficientFFA/MSM/Tables.lean#L68), [C.table_lookup_sound](EfficientFFA/MSM/Tables.lean#L185). Accepted raw table equations, on-curve base/start and the initial x-distinctness premise establish the group meaning of every table entry. |
| **T02** — §4.5, p.10, table-construction paragraph | The table recurrence implies internal validity/distinctness without extra per-entry guards. | Covered | [EC.x_ne_of_add_checks](EfficientFFA/MSM/Tables.lean#L28), [C.repeated_step](EfficientFFA/MSM/Tables.lean#L49), [C.table_guards](EfficientFFA/MSM/Tables.lean#L89), [C.table_sound](EfficientFFA/MSM/Tables.lean#L68), [C.table_safe](EfficientFFA/MSM/Tables.lean#L119). This is a soundness theorem about accepted table equations. Lean does not add per-entry guard constraints. |
| **T03** — §4.5, p.10, table-construction paragraph | Suitable offsets admit witnesses for all table equations. | Conditional | [MSM.TableSafe](EfficientFFA/MSM/Tables.lean#L14), [C.table_complete](EfficientFFA/MSM/Tables.lean#L142), [MSM.table_safe_iff_avoids](EfficientFFA/MSM/TableOffsets.lean#L24), [MSM.badOffsets_card_le](EfficientFFA/MSM/TableOffsets.lean#L61). The first x-distinctness check alone does not guarantee table witness existence (e.g. V=2P can fail later). This is handled by offset selection and rejection bounds, not by adding a new MSM guard. |
| **T04** — §4.5, pp.9–10, choosing U and constants | Select parameters giving safe table setup with few excluded seeds. | Conditional | [MSM.badSeeds_card_le](EfficientFFA/MSM/Parameters.lean#L25), [MSM.exists_safe_setup_prime](EfficientFFA/MSM/Parameters.lean#L79), [C.tables_exist_of_parameters](EfficientFFA/MSM/Parameters.lean#L101). Lean makes the paper’s qualitative claim quantitative: setup excludes at most 1+l*(b+1) seeds when steps=b−1 and the required scalar maps are injective. Existence requires this budget below group size. |
| **T05** — Figure 4 Steps 1–5, p.10; footnote 6, p.9 | Tie supplied constants and table origins to a single random seed U. | Covered | [C.scale_sound](EfficientFFA/MSM/Chains.lean#L16), [C.scale_exists](EfficientFFA/MSM/Chains.lean#L47), [C.trace_setup](EfficientFFA/MSM/Trace.lean#L48), [E.scale_iff](EfficientFFA/Native/Trace.lean#L88), [E.trace_iff](EfficientFFA/Native/Trace.lean#L116). The trace verifies the scalar-multiplication links for V and the initial accumulator, rather than merely assuming unlinked constants. Complete-addition chains implement these links semantically; the particular cheap chain/circuit layout is not verified. |
| **T06** — Figure 4 Step 10, p.10; footnote 7, p.9 | A bounded window selects its corresponding table entry. | Covered | [C.table_lookup_sound](EfficientFFA/MSM/Tables.lean#L185), [C.trace_lookup](EfficientFFA/MSM/Trace.lean#L58), [MSM.descending_range](EfficientFFA/MSM/TraceStatistics.lean#L6). Lookup selection is a mathematical relation with bounded indices, not a verification of the PLONK lookup argument or table layout. |
| **T07** — §4.5, p.9; Figure 4 Steps 6–13, p.10 | Each window cancels its introduced offsets while retaining lU. | Covered | [MSM.addRows_eq](EfficientFFA/MSM/Loop.lean#L15), [MSM.loop_invariant](EfficientFFA/MSM/Loop.lean#L34), [MSM.row_invariant](EfficientFFA/MSM/Loop.lean#L89), [MSM.rowValue](EfficientFFA/MSM/Loop.lean#L82), [MSM.offsetCoeff](EfficientFFA/MSM/Loop.lean#L86), [C.trace_rows](EfficientFFA/MSM/Trace.lean#L96), [C.trace_boundaries](EfficientFFA/MSM/Trace.lean#L114). The row coefficient is b*l−(b−1)*j. The proof uses actual table identities and repeated doubling/addition relations. |
| **T08** — Figure 4 scalar expansion and Step 6, p.10 | The final accumulator represents the intended window expansion. | Refined | [MSM.horner_eq_sum](EfficientFFA/MSM/Loop.lean#L48), [MSM.descending](EfficientFFA/MSM/Loop.lean#L64), [MSM.loop_correct](EfficientFFA/MSM/Loop.lean#L68), [C.trace_sound_littleEndian](EfficientFFA/MSM/Trace.lean#L151), [E.trace_sound_littleEndian](EfficientFFA/Native/Trace.lean#L157). The printed expansion is little-endian but the printed Horner loop traverses forward. Lean traverses windows in descending order, producing Σ_i b^i*window(i,j). It does not verify the literal forward loop against that expansion. |
| **T09** — Figure 4 Steps 8, 11–13, p.10 | Intermediate additions and doublings can use finite/incomplete operations. | Conditional | [MSM.addRows_ne_zero](EfficientFFA/MSM/Safety.lean#L7), [MSM.loop_ne_zero](EfficientFFA/MSM/Safety.lean#L19), [MSM.row_ready](EfficientFFA/MSM/Safety.lean#L37), [MSM.doubling_ready](EfficientFFA/MSM/Safety.lean#L57), [C.trace_complete](EfficientFFA/MSM/TraceCompleteness.lean#L162). Required nonidentity states follow from the accepted group execution and invertible radix map. The loop retains its printed x-distinctness check; table-internal guards remain derived. |
| **T10** — Figure 4 Steps 14–15, p.10 | Subtract lU and return the correct MSM, including a possible infinity output. | Covered | [C.trace_sound](EfficientFFA/MSM/Trace.lean#L134), [C.trace_sound_littleEndian](EfficientFFA/MSM/Trace.lean#L151), [E.trace_sound_littleEndian](EfficientFFA/Native/Trace.lean#L157). Applies to every accepted full trace with valid finite bases. The final subtraction uses complete addition. This includes native limb constraints under the ECEncoding contract. |
| **T11** — §4.5, p.10, statistical-completeness argument | Each potential loop collision excludes only a small number of seeds. | Conditional | [MSM.collision_iff](EfficientFFA/MSM/Collisions.lean#L29), [MSM.collision_coeff_bounds](EfficientFFA/MSM/Collisions.lean#L45), [MSM.collisionSeeds_card_le](EfficientFFA/MSM/Collisions.lean#L93), [MSM.loopBadSeeds_card_le_prime](EfficientFFA/MSM/Collisions.lean#L132). The two affine collision equations each exclude at most one seed when their scalar coefficients are injective. A sufficient prime-order condition is b*l+b−1 < N. |
| **T12** — §4.5, pp.9–10, “negligible” abort probability | Uniform seed choice makes MSM witness failure unlikely. | Conditional | [MSM.failureBudget](EfficientFFA/MSM/Rejection.lean#L13), [MSM.uniform_group_failure_bound_prime](EfficientFFA/MSM/Rejection.lean#L125), [C.uniform_littleEndian_trace_failure_bound_prime](EfficientFFA/MSM/TraceStatistics.lean#L41), [E.uniform_littleEndian_failure_bound](EfficientFFA/Native/Statistics.lean#L21). For b=2^w, l bases, t windows and prime group order N with w,l>0 and b*l+b−1<N, failure probability is at most (1+l*(b+1)+2*t*l)/N. Bases/windows are fixed before uniform sampling. A negligible asymptotic bound additionally requires a suitable parameter family; no such asymptotic theorem is stated. |
| **T13** — §4.5, statistical completeness and no-guard table construction | Successful abstract executions admit coordinate and native witnesses. | Covered | [C.trace_complete](EfficientFFA/MSM/TraceCompleteness.lean#L162), [C.TraceWitnesses](EfficientFFA/MSM/TraceCompleteness.lean#L63), [E.traceWitnesses_iff](EfficientFFA/Native/Statistics.lean#L13), [E.exists_correct_trace](EfficientFFA/Native/Statistics.lean#L34). The probability event is absence of any accepted trace, not failure of an unspecified runtime witness generator. Existence of a good seed additionally needs the failure budget below group order. |
| **T14** — §4 opening, p.7; §4.2, p.8; §4.5 | The MSM argument can operate inside a prime-order subgroup of a larger curve group. | Conditional | [MSM.groupAccepts_map_iff](EfficientFFA/MSM/Embedding.lean#L31), [C.trace_complete_subgroup](EfficientFFA/MSM/Subgroup.lean#L16), [E.uniform_subgroup_failure_bound](EfficientFFA/Native/Subgroup.lean#L38), [E.uniform_subgroup_failure_bound_checked](EfficientFFA/Native/Subgroup.lean#L67), [E.exists_correct_subgroup_trace](EfficientFFA/Native/Subgroup.lean#L50). Sample uniformly in H and use N=card H. The ambient group need not have prime order. Known subgroup membership suffices for the bound; using the native annihilation-based membership test additionally needs coprime cofactor. The sample includes zero, which is counted among excluded seeds. |
| **T15** — §4.5, p.10, GLV paragraph | GLV can further optimize the MSM and is used in the implementation. | Unmapped | **No direct counterpart.** No GLV endomorphism, scalar decomposition, correctness theorem or cost comparison is present. |
| **T16** — §4.5, p.10, negation of V | Negating y and preserving x/flag represents group negation. | Covered | [C.point_opposite](EfficientFFA/MSM/Tables.lean#L204), [C.coordinates_neg](EfficientFFA/MSM/TraceCompleteness.lean#L33), [E.opposite_iff](EfficientFFA/Native/Trace.lean#L28). The native opposite relation links the encoded constants used for table starts and the final correction. |

### Background, implementation and applications

| ID and paper location | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **B01** — Abstract; §§1–2, pp.1–4; references, pp.12–13 | SNARK/PLONK security, succinctness, setup, recursion, cycles, lookup/permutation arguments and cited applications. | Background | **No direct counterpart.** These are cited foundations and motivation, not results proved by this arithmetic library. No reduction establishes knowledge soundness or zero knowledge of a PLONK proof system. Bibliographic assertions are grouped here, not counted as new paper theorems. |
| **B02** — §1.2, pp.2–3; §1.3, p.3 | Comparison with earlier FFA schemes and favorable auxiliary-modulus choices. | Partial | [M.residual_bounds](EfficientFFA/Multiplication/Bounds.lean#L57), [M.auxCore_bounds](EfficientFFA/Multiplication/Bounds.lean#L71). Actual weighted bounds support the arithmetic contribution. Claims about previous implementations, eliminating terms with power-of-B moduli, often needing one fewer modulus, or relative efficiency are not general comparison/optimization theorems. |
| **B03** — Abstract; §1, pp.1–2; §§6.1–6.3, pp.11–12 | Emulation overhead is about one order of magnitude and enables efficient arbitrary-curve applications. | Unmapped | **No direct counterpart.** These are implementation/benchmark conclusions, not consequences of the arithmetic acceptance equivalences alone. |
| **I01** — §3.1.3, p.6; §5, p.10; [AFQ25], p.12 | EasyCrypt proves the multiplication results; the cited development uses Jasmin limbs/SMT, is about 1K LOC, and EC work was ongoing. | Unmapped | **No direct counterpart.** Historical provenance/status assertions are not Lean theorems. M10–M11 give independent mathematical counterparts; they do not certify the cited sound-and-complete-ffa release or establish equivalence of the two developments. |
| **I02** — §2, p.4; §6, pp.10–11; footnote 8 | The Halo2/PSE KZG implementation uses gates spanning ≤3 rows, degree ≤6, four parallel ≤16-bit lookups and typically 2n+1 columns. | Unmapped | **No direct counterpart.** No implementation refinement, layout compiler, permutation/lookup protocol proof, row/degree accounting or production witness generator is verified. Native expression compilation concerns mathematical polynomials, not this circuit architecture. |
| **I03** — §6, p.10 | The implementation is parametric over emulated/parent curves and supports blockchain precompiles. | Partial | [Native.ECEncoding](EfficientFFA/Native/EllipticCurve.lean#L28). Lean is parameterized over a prime foreign field and an explicit valid encoding. This does not prove compatibility of the Halo2 implementation with Ethereum/Cardano/Solana or a deployed verifier. |
| **P01** — Table 2, p.10; §6.1, p.11, n=3 | Three-limb parameter set and measured resource costs. | Unmapped | **No direct counterpart.** B=2^86, M={2^86,2^86−1}; 8 columns; 5600*l+7300 rows; 4.92/4.40 KB (BLS12-381/BN254). Neither production parameter validity nor these costs are instantiated in Lean. |
| **P02** — Table 2, p.10; §6.1, p.11, n=4 | Four-limb parameter set and measured resource costs. | Unmapped | **No direct counterpart.** B=2^64, M={2^128}; 9 columns; 3900*l+5000 rows; 5.09/4.56 KB. No production validity or resource theorem. |
| **P03** — Table 2, p.10; §6.1, p.11, n=5 | Five-limb parameter set and measured resource costs. | Unmapped | **No direct counterpart.** B=2^52, M={2^156}; 11 columns; 4060*l+5500 rows; 5.37/4.81 KB. No production validity or resource theorem. |
| **P04** — Table 2, p.10; §6.1, p.11, n=6 | Six-limb parameter set and measured resource costs. | Unmapped | **No direct counterpart.** B=2^44, M={2^172}; 13 columns; 4360*l+5850 rows; 5.65/5.06 KB. No production validity or resource theorem. |
| **P05** — §6.1, p.11 | Four limbs are the most efficient of the compared configurations. | Unmapped | **No direct counterpart.** This is a benchmark-based choice for the evaluated implementation, not a theorem minimizing circuit size over all valid parameters. |
| **P06** — §6.2, p.11, ECDSA.Sign / ECDSA.Verify | ECDSA signing/verification equations and their implementation. | Unmapped | **No direct counterpart.** No ECDSA correctness/security theorem or verification-circuit specification is present. MSM correctness alone does not certify this application, its inversions, scalar reductions or exceptional cases. |
| **P07** — §6.2, pp.11–12, two PoK relations | Prove knowledge of t distinct valid signatures with keys in raw S or Poseidon-committed S. | Unmapped | **No direct counterpart.** Neither application relation, membership/distinctness composition, Poseidon commitment nor proof-of-knowledge property is formalized. |
| **P08** — Figure 5, p.11; §6.2, p.12 | Raw-S verification is linear; committed-S verification is constant; prover timings exhibit FFT-size jumps and hashing overhead. | Unmapped | **No direct counterpart.** Empirical times for both parent curves and explanations of cost are not Lean results. This map does not rerun or validate the measurements. |
| **P09** — §6.3, p.12 | Self-recursive PLONK verification uses accumulation to defer KZG pairings. | Unmapped | **No direct counterpart.** No PLONK verifier, accumulation scheme, pairing deferral, counter application or recursive composition theorem is formalized here. |
| **P10** — §6.3, p.12, self-emulation parameter sets | BLS12-381 and BN254 support the reported self-emulation configurations. | Unmapped | **No direct counterpart.** BLS: B=2^56, n=7, M={2^136,2^136−2}; BN: B=2^52, n=6, M={2^142}. These production arithmetic obligations have not been discharged in this repository. |
| **P11** — Table 3, p.12 | Self-recursion has the reported proof sizes, times and circuit sizes. | Unmapped | **No direct counterpart.** BLS: 6.10 KB, 11 ms verifier, 35 s prover, 241K rows, 15 columns. BN: 4.71 KB, 9 ms, 29 s, 177K rows, 11 columns. No benchmark or cost theorem. |
| **P12** — §6.3, p.12, conclusion | Foreign-field self-recursion is simpler/less error-prone than cycle-based approaches and suitable for fixed proving systems. | Unmapped | **No direct counterpart.** This is a qualitative engineering assessment, not a formal comparative reliability result. |

## What this map leaves open

The main arithmetic results and the corrected EC/MSM semantics have formal
counterparts. An exact match to the paper still requires its presentation to
record the quotient-rounding convention, unit condition for general-modulus
division, ordered complete-add branches, window traversal, and explicit
statistical parameter conditions. No paper edits are made by this inventory.

The genuine scope gaps are shifted EC/native-trace integration (E09), GLV
(T15), production parameter instances (P01–P04, P10), and implementation,
resource, application and cryptographic-protocol claims (I01–I03, P05–P12).
Some are appropriate future formalization tasks; measurements and historical
claims need reproducible evidence rather than an invented Lean theorem.
Production instances and circuit work remain deferred under the existing plan.

Additional Lean results support the paper without being separately stated
there: exact finite rejection budgets; arbitrary accepted-trace soundness;
subgroup membership/cofactor conditions; and small concrete curve regressions.
Those strengthen or clarify coverage, but do not validate the production
parameters or benchmark results. Tests/Parameters.lean, Tests/Native.lean,
Tests/Trace.lean and Tests/Subgroup.lean provide checked examples/counterexamples;
anonymous test examples are supporting evidence rather than named paper theorems.

## Validation and maintenance

The default `lake build` includes Tests.PaperCorrespondence and checks all
236 distinct referenced declarations, together with the existing library
and regression suite. No library proof or acceptance definition was changed
for this mapping. The existing 319 library theorem axiom reports continue to
use only the standard Lean axioms (or none); the reference index adds no theorems.

When a statement changes, review its row's assumptions and status as well as
updating the source link and checked reference. A successful build detects
missing/renamed declarations; it cannot detect a subtly changed mathematical
contract or prove that a paper sentence was interpreted correctly.
