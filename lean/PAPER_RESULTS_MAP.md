# Current paper claims mapped to Lean

Updated: 2026-11-12. Paper: [miguel-ambrona/ffa-paper](https://github.com/miguel-ambrona/ffa-paper/tree/a811ec79ffd29008ee72c1b0c927ba1414599758)
at `a811ec79ffd29008ee72c1b0c927ba1414599758`. Lean foundation for this
update: `a4e2a53eccfb0bcd99c304edad3df8007120b096`, plus the paper-facing
interface and arithmetic/shifted-EC closure described below.

This is a **Lean-only theoretical coverage inventory**. Other formalizations
supply no evidence for its verdicts. The paper has not been edited. Corrected
contracts below are proposed mathematical specifications, not a claim that
the printed algorithms already say the same thing.

The source has four theorem statements: `thm:mul`, `thm:mul-soundness`,
`thm:mul-completeness` and `thm:msm`. Normalization still has a theorem TODO.
We use source labels and descriptive anchors because moving material into the
appendix and adding a multiplication figure changed numbering. Every source
link below is pinned to the reviewed commit. Stable claim IDs are retained;
M12 is the new combined multiplication theorem and L12 separates the modulus-
reuse obligation from the accumulation claim in L11.

## Coverage contract

Completion means every in-scope theoretical claim has a theorem with matching
hypotheses, or an explicit correction supported by a theorem/counterexample.
A counterexample does not prove the printed claim: publication correspondence
still requires adopting its corrected statement. Existing proofs with
uninstantiated numerical assumptions do not certify the production tables.

| Status | Meaning |
|---|---|
| Covered | The mathematical claim has a proof under the stated explicit assumptions. Numerical instantiation can remain a separate claim. |
| Conditional | The proof exists, but its material input/group/parameter hypotheses must be stated in the paper. |
| Refined | Lean proves the corrected contract; the printed formulation or explanation differs. See the correction register. |
| Partial | Some mathematics is proved, but an identified part of the claim remains open. |
| Open | A required mathematical proof or concrete parameter instantiation is missing. |
| Excluded | Implementation, cost, performance, application, attribution or external background; not an obligation of this milestone. |

The 92 rows are claim families, not a theorem count or coverage percentage.
PLONK layout, range-check lookup implementation, whole-MSM shared wiring,
performance, GLV implementation and application/cryptographic-protocol proofs
are excluded. Deterministic validity of the reported arithmetic parameters,
normalization modulus reuse and shifted EC identities are in scope.

## Paper-facing theorem interface

All names in this table are in `EfficientFFA.Paper` and have their complete
binders in [Paper.lean](EfficientFFA/Paper.lean) and
[Paper/MSMContract.lean](EfficientFFA/Paper/MSMContract.lean). They are proved wrappers around
existing results, not new axioms or replacement acceptance definitions.

| Source claim | Interface declarations | Contract distinction |
|---|---|---|
| thm:mul (M12) | multiplication_iff | Valid parameters and bounded supplied x/y/z; no output canonicality claim. |
| thm:mul-soundness (M10) | multiplication_sound | Positive parameters and NoWrap; width adequacy is not needed for this direction. |
| thm:mul-completeness (M11) | multiplication_complete | Positive parameters and WidthBounds; NoWrap is not needed for this direction. |
| eq:normalization and theorem TODO (L09–L10) | normalization_iff, normalization_exists | Validity establishes equivalence; capacity constructs a canonical output. |
| Signed native storage (L06) | stored_normalization_sound | Native checks operate on residues representing tracked bounded signed integers. |
| Corrected fig:complete-add (O04–O06) | complete_add_sound, complete_add_complete | Valid inputs and ordered coordinate branches; handles infinity and two-torsion. |
| Native selector realization (E08/O04/O05) | native_complete_add_iff | Native prime, B≤p, valid encoding and inputs; shared limbs inside this gadget. |
| thm:msm soundness (T17) | msm_sound | Arbitrary accepted linked trace, valid finite bases, descending little-endian windows. |
| thm:msm statistical completeness (T17) | msm_failure_bound, msm_subgroup_failure_bound | Normalized uniform seed, fixed inputs, prime group/subgroup order and size conditions. |
| Combined thm:msm contracts (T17) | msm_contract, msm_subgroup_contract | Universal soundness, the finite failure bound and conditional witness existence in one statement; the existence budget remains a separate premise. |
| Successful-seed corollaries (T14/T17) | msm_exists_correct, msm_exists_correct_subgroup | Additionally require the failure budget to be strictly below group cardinality. |

## Corrected mathematical specification and evidence

| ID | Required formulation | Existing evidence / remaining obligation |
|---|---|---|
| C01 — window order (T08) | For scalar Σ_i b^i s_i, process i=T−1 down to 0. | MSM.loop_correct and Paper.msm_sound. Tests/MSM.lean checks digits (1,2), radix 4: descending gives 9, forward gives 6. The literal printed traversal does not have the claimed result. |
| C02 — complete addition (O04–O06) | If P is infinity, copy Q; otherwise if Q is infinity, copy P; otherwise handle inverse inputs first, then doubling or distinct-x addition. | Paper.complete_add_sound/complete_add_complete and native_complete_add_iff. Tests.PaperAudit.single_infinity_literal_conflict disproves the printed coordinate-only inverse overlap; Curve.identity_copies_iff records the two-infinity conflict. |
| C03 — table guards (T02–T03) | Valid base/start, initial x-distinctness and accepted recurrence equations imply later guards. Witness existence is a separate safe-offset assertion. | Curve.table_guards, table_witnesses_iff and offset_table_witnesses_iff. Tests/Tables.lean checks V=2P: the initial guard passes but no complete table witnesses exist. No per-entry MSM guard is added. |
| C04 — division (D01) | For arbitrary q, require the divisor to be a unit; nonzero suffices over a prime field. | Division.inverse_exists_iff_coprime and encoded_division_iff; composite-modulus counterexamples in Tests/LazyNormalization.lean. |
| C05 — doubling (E04/O01/O02) | Finite doubling witnesses exist exactly when 2y≠0; the output-y equation needs no x(R)−x(P) inverse. | Curve.doubling_witnesses_iff, flagged_double_witnesses_iff and output_determined. Tests/EllipticCurve.lean includes a valid order-three doubling with unchanged x. No order-three exclusion is needed. |
| C06 — indices and scaling (M10/M11/L05) | Use n limbs indexed 0≤i<n; scale input interval endpoints, swapping them for negative constants. | Limbs is Fin n→ℤ; LazyArithmetic.bounded_scale proves the rule. The appendix’s inclusive n and table’s self-referential z bounds need correction. |
| C07 — rounding (M04) | Lower quotient endpoints use ceiling; upper endpoints use floor, including negative upper numerators. | Lean quotient_interval and parameter definitions prove this convention. Paper.lower_trunc_eq and floor_width_of_trunc prove compatibility at unchanged widths; multiplication_valid_of_trunc requires the actual NoWrap proof. No increased-width no-wrap claim is made. |
| C08 — statistical theorem (T17) | State the exact sampling event, budget and hypotheses below; distinguish a finite bound from asymptotic negligibility. | Paper.msm_failure_bound / msm_subgroup_failure_bound and the separate existence corollaries. The source already says statistically complete but leaves the bound/contract as TODOs. |

For C08 put b=2^W, use l bases and T windows. Fix the bases and windows
independently of the seed. Finite on-curve coordinates represent nonidentity
bases; the interfaces currently express validity for the full base function,
including unused indices. Used windows are in [0,b). For a prime-order group
or subgroup H of size N, with W,l>0 and b*l+b−1<N, sample U uniformly from
**all** of H, including the identity. The proved event is absence of any
accepting native arithmetic trace with that seed:

~~~text
Pr_U[no accepting trace with seed U] ≤ (1 + l*(b+1) + 2*T*l) / N.
~~~

The +1 includes rejected identity seeds; setup/table failures and loop
collisions are all counted. The inequality does not require budget<N; that
strict condition is needed for the existence corollary. No adaptive choice
of inputs after seeing U is covered by this fixed-input probability theorem.
An asymptotic negligibility claim needs a specified parameter family and a
proof that the ratio is negligible; the present target is the explicit bound.

Arithmetic validity is supplied by ECEncoding: capacity and per-identity
positivity, widths and no-wrap conditions. Native primality and B≤p are
additional explicit conditions for the separate shared-limb selector theorem;
they are not silently added as statistical group-order assumptions. Subgroup
probability assumes membership; using the native loading test to establish
membership additionally needs the coprime-cofactor condition in E.member_iff.

## Reference notation

Existing declaration references below use these namespace abbreviations;
`Paper` means `EfficientFFA.Paper`. Definitions identify a contract and are
not counted as proofs. Tests/PaperCorrespondence.lean checks declaration names;
semantic correspondence remains a reviewed mathematical judgment.

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


## Claim inventory

### Foundations and representation

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **F01** — [appendix.tex · sec:sound-and-compl-of-mult](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L145) | Simultaneous modular equalities combine modulo the LCM. | Covered | [A.moduliLCM](EfficientFFA/Arithmetic.lean#L14), [A.congruent_all_iff_lcm](EfficientFFA/Arithmetic.lean#L19). No pairwise-coprimality assumption is needed. This is the LCM form of the CRT argument, not reconstruction of arbitrary unrelated residues. |
| **F02** — [appendix.tex · sec:sound-and-compl-of-mult](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L145) | A bounded integer divisible by all selected moduli must be zero. | Covered | [A.eq_zero_of_congruences_of_bounds](EfficientFFA/Arithmetic.lean#L43), [A.eq_zero_of_modEq_of_bounds](EfficientFFA/Arithmetic.lean#L29). Strict signed bounds relative to the positive LCM are essential. |
| **F03** — [ffa.tex · sec:ffa](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L4) | Little-endian limb representation and capacity B^n ≥ q. | Covered | [A.eval](EfficientFFA/Limbs.lean#L16), [A.WellFormed](EfficientFFA/Limbs.lean#L20), [A.exists_limbs](EfficientFFA/Representation.lean#L7), [A.exists_canonical_limbs](EfficientFFA/Representation.lean#L41), [A.eval_bounds](EfficientFFA/Representation.lean#L59). Existence requires capacity and a valid base. Lean does not require n to be the smallest possible length. |
| **F04** — [ffa.tex · Division and comparisons](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L171) | Bounded integer representations are unique; residue representations can be noncanonical. | Covered | [A.eval_injective](EfficientFFA/Representation.lean#L70), [Paper.residue_injective](EfficientFFA/Paper/Arithmetic.lean) and [Paper.duplicate_residues_iff](EfficientFFA/Paper/Arithmetic.lean). For B,q>0, bounded residue encodings have duplicates exactly when q<B^n; B^n≤q gives injectivity. Canonical output still needs an explicit [0,q) bound. |
| **F05** — [ffa.tex · sec:ffa](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L4) | Limbs fit natively for suitable B; sufficient headroom is needed for computation. | Refined | [Paper.limb_product_lt_native](EfficientFFA/Paper/Arithmetic.lean) and [Paper.two_limbs_of_headroom](EfficientFFA/Paper/Arithmetic.lean) give precise sufficient conditions: B²<p prevents individual limb-product wrap; additionally p≤q² and q≤B^n force n≥2. Every production configuration proves radix_headroom. Weighted residual checks still require the separate Valid conditions. This replaces the informal “well below” heuristic, without an optimization claim. |

### Multiplication

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **M01** — [ffa.tex · eq:mul-over-z](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L35) | Expand a product of limb evaluations. | Covered | [A.eval_mul](EfficientFFA/Limbs.lean#L29). Exact integer identity. |
| **M02** — [ffa.tex · eq:mul-over-z](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L35) | Reduce coefficients modulo q and introduce an integer quotient k. | Covered | [A.mulResidual_mod](EfficientFFA/Limbs.lean#L42), [A.mulResidual_dvd_iff](EfficientFFA/Limbs.lean#L49), [A.multiplication_iff_quotient](EfficientFFA/Limbs.lean#L54). Equivalence is with modular multiplication, not integer equality of the original operands. |
| **M03** — [appendix.tex · app:ffmul](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L3) | Weighted coefficient sums give the displayed tighter lower and upper bounds. | Covered | [MB.weighted_sum_bounds](EfficientFFA/Multiplication/Bounds.lean#L7), [MB.weighted_product_bounds](EfficientFFA/Multiplication/Bounds.lean#L22), [M.residual_bounds](EfficientFFA/Multiplication/Bounds.lean#L57). Bounds use actual reduced coefficients and bounded limbs. No theorem claims a strict improvement for every parameter choice or a smaller circuit for every input. |
| **M04** — [appendix.tex · quotient rounding](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L31) | Derive k and auxiliary quotient intervals by rounding. | Refined | [MB.quotient_interval](EfficientFFA/Multiplication/Bounds.lean#L49), [M.kmin](EfficientFFA/Multiplication/Definitions.lean#L31), [M.kmax](EfficientFFA/Multiplication/Definitions.lean#L32), [M.lmin](EfficientFFA/Multiplication/Definitions.lean#L44), [M.lmax](EfficientFFA/Multiplication/Definitions.lean#L45). Negative lower endpoints use the ceiling convention. Lean floors the auxiliary upper quotient even when its numerator is negative; the appendix rounding footnote prescribes truncation toward zero. Lean’s upper bound is then tighter and remains valid. [Paper.lower_trunc_eq](EfficientFFA/Paper/Rounding.lean) identifies lower shifts; floor_width_of_trunc and multiplication_valid_of_trunc prove the compatibility implication at unchanged widths with actual no-wrap conditions. |
| **M05** — [appendix.tex · eq:mul-over-z-on-u](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L52) | Shift k to u and range-check it in a power-of-two interval. | Covered | [M.nativeResidual](EfficientFFA/Multiplication/Definitions.lean#L47), [M.Umax](EfficientFFA/Multiplication/Definitions.lean#L33), [M.WidthBounds](EfficientFFA/Multiplication/Definitions.lean#L76), [M.Accepts](EfficientFFA/Multiplication/Definitions.lean#L93). Widths need only be sufficient, not minimal. Increasing them requires rechecking NoWrap; choosing too small a width can lose completeness. |
| **M06** — [appendix.tex · sec:sound-and-compl-of-mult](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L145) | Native and auxiliary congruences plus the LCM bounds reconstruct the integer equation. | Covered | [M.nativeResidual_bounds](EfficientFFA/Multiplication/Bounds.lean#L88), [M.NoWrap](EfficientFFA/Multiplication/Definitions.lean#L80), [M.multiplication_sound](EfficientFFA/Multiplication/Soundness.lean#L16). The native p check and every auxiliary check are part of acceptance. |
| **M07** — [ffa.tex · eq:mul-mod-m](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L56) | Reduce coefficients again modulo m and introduce the shifted auxiliary quotient. | Covered | [M.auxCore](EfficientFFA/Multiplication/Definitions.lean#L51), [M.auxResidual](EfficientFFA/Multiplication/Definitions.lean#L56), [M.auxCore_congr](EfficientFFA/Multiplication/Soundness.lean#L8), [M.auxCore_bounds](EfficientFFA/Multiplication/Bounds.lean#L71). The constant (kmin*q) mod m is reduced as a whole; auxiliary quotient ranges are explicit. |
| **M08** — [appendix.tex · eq:upper-bound](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L138) | The two auxiliary residual bounds prevent wraparound modulo p. | Covered | [M.auxResidual_bounds](EfficientFFA/Multiplication/Bounds.lean#L98), [M.NoWrap](EfficientFFA/Multiplication/Definitions.lean#L80). Strict bounds are checked for each auxiliary modulus. |
| **M09** — [figures/ffmul.tex · fig:ffmul](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/ffmul.tex#L28) | Combined multiplication gate: native identities, quotient ranges, bounded output. | Covered | [M.Accepts](EfficientFFA/Multiplication/Definitions.lean#L93), [M.accepts_iff_multiplication](EfficientFFA/Multiplication.lean#L7). WellFormed assumptions on x,y,z are separate from Accepts. No PLONK lookup or range-check implementation is verified. |
| **M10** — [appendix.tex · thm:mul-soundness](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L210) | Every accepting bounded triple represents multiplication modulo q. | Covered | [M.multiplication_sound](EfficientFFA/Multiplication/Soundness.lean#L16). Requires Positive and NoWrap plus bounded x,y,z and acceptance. WidthBounds and representational capacity are unnecessary for this direction once the triple is supplied. Paper-facing endpoint: [Paper.multiplication_sound](EfficientFFA/Paper.lean). |
| **M11** — [appendix.tex · thm:mul-completeness](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L249) | Every correct bounded multiplication triple admits accepting quotient witnesses. | Covered | [M.canonical_witnesses_accept](EfficientFFA/Multiplication/Completeness.lean#L16), [M.multiplication_complete](EfficientFFA/Multiplication/Completeness.lean#L53). Requires Positive and WidthBounds plus bounded x,y,z and modular multiplication. NoWrap is unnecessary for witness existence. This supplies witnesses for a given z, not a proof that every residue has a bounded representation without capacity. Paper-facing endpoint: [Paper.multiplication_complete](EfficientFFA/Paper.lean). |
| **M12** — [ffa.tex · thm:mul](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L91) | Main multiplication theorem: acceptance iff modular multiplication. | Covered | [Paper.multiplication_iff](EfficientFFA/Paper.lean). Combines M10/M11 for bounded supplied x/y/z and a Valid parameter bundle. Capacity is needed for arbitrary output construction, not this supplied-triple equivalence. The rounding bridge in [M04](EfficientFFA/Paper/Rounding.lean) is now proved. |

### Lazy operations and normalization

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **L01** — [figures/ops-table.tex · tab:ffa-ops](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/ops-table.tex#L11) | Limb-wise addition preserves the represented value and adds limb bounds. | Covered | [A.eval_add](EfficientFFA/Limbs.lean#L72), [L.bounded_add](EfficientFFA/LazyArithmetic.lean#L14), [L.represents_add](EfficientFFA/LazyArithmetic.lean#L56). Tracked integer lifts justify native arithmetic without inserting a fresh range check after each addition. |
| **L02** — [figures/ops-table.tex · tab:ffa-ops](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/ops-table.tex#L11) | Limb-wise subtraction works with signed lifts, including native wraparound. | Covered | [A.eval_sub](EfficientFFA/Limbs.lean#L76), [L.bounded_sub](EfficientFFA/LazyArithmetic.lean#L22), [L.represents_sub](EfficientFFA/LazyArithmetic.lean#L62). The lower endpoint subtracts the other upper endpoint, and conversely. Stored residues must represent the tracked lifts. |
| **L03** — [figures/ops-table.tex · tab:ffa-ops](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/ops-table.tex#L11) | Negation reverses and negates interval endpoints. | Covered | [L.eval_neg](EfficientFFA/LazyArithmetic.lean#L83), [L.bounded_neg](EfficientFFA/LazyArithmetic.lean#L30), [L.represents_neg](EfficientFFA/LazyArithmetic.lean#L68). Uses signed integer lifts. |
| **L04** — [figures/ops-table.tex · tab:ffa-ops](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/ops-table.tex#L11) | Add a constant limb-wise and update bounds. | Covered | [L.bounded_add_constant](EfficientFFA/LazyArithmetic.lean#L36), [L.represents_add_constant](EfficientFFA/LazyArithmetic.lean#L73). The constant is supplied with its limb values. |
| **L05** — [figures/ops-table.tex · tab:ffa-ops](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/ops-table.tex#L11) | Scale limbs, swapping bound endpoints for a negative constant. | Refined | [A.eval_scale](EfficientFFA/Limbs.lean#L80), [L.bounded_scale](EfficientFFA/LazyArithmetic.lean#L41), [L.represents_scale](EfficientFFA/LazyArithmetic.lean#L78). The printed bound row refers to output z where it needs input x bounds. Lean states the rule using the input bounds and handles either sign. |
| **L06** — [ffa.tex · sec:other-ops](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L114) | Compose lazy operations while keeping bounds inside the normalization limit. | Covered | [L.represents_reduced](EfficientFFA/LazyArithmetic.lean#L51), [N.stored_normalization_sound](EfficientFFA/Normalization.lean#L52), [N.stored_normalization_exists](EfficientFFA/Normalization.lean#L59), [N.subtraction_normalization_sound](EfficientFFA/Normalization.lean#L67). Soundness uses a bounded lift, not small unsigned stored residues. Exceeding the stated limit leaves this theorem’s domain; it is not an impossibility theorem for every normalization scheme. Paper-facing endpoint: [Paper.stored_normalization_sound](EfficientFFA/Paper.lean). |
| **L07** — [ffa.tex · eq:normalization](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L157) | Coefficient-reduced linear equality characterizes normalization. | Covered | [NB.residual_mod](EfficientFFA/Normalization/Definitions.lean#L14), [NB.residual_dvd_iff](EfficientFFA/Normalization/Definitions.lean#L18), [NB.normalization_iff_quotient](EfficientFFA/Normalization/Definitions.lean#L23). Normalization preserves the foreign residue. |
| **L08** — [ffa.tex · eq:normalization](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L157) | Bound the normalization residual from signed input bounds. | Covered | [NB.weighted_linear_bounds](EfficientFFA/Normalization/Bounds.lean#L7), [N.residual_bounds](EfficientFFA/Normalization/Bounds.lean#L25). Includes the displayed conservative lower bound using limit+B. |
| **L09** — [ffa.tex · eq:normalization](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L157) | Native/auxiliary normalization checks are sound and complete. | Covered | [N.auxCore_congr](EfficientFFA/Normalization/Soundness.lean#L8), [N.auxCore_bounds](EfficientFFA/Normalization/Bounds.lean#L32), [N.nativeResidual_bounds](EfficientFFA/Normalization/Bounds.lean#L44), [N.auxResidual_bounds](EfficientFFA/Normalization/Bounds.lean#L54), [N.normalization_sound](EfficientFFA/Normalization/Soundness.lean#L16), [N.normalization_complete](EfficientFFA/Normalization/Completeness.lean#L54), [N.accepts_iff_normalization](EfficientFFA/Normalization.lean#L8). Lean fills in the omitted auxiliary construction with explicit positivity, width, no-wrap and limb-bound hypotheses. Paper-facing endpoint: [Paper.normalization_iff](EfficientFFA/Paper.lean). |
| **L10** — [ffa.tex · eq:normalization](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L157) | A bounded lazy input can be normalized to a well-formed output. | Covered | [N.normalization_exists](EfficientFFA/Normalization.lean#L17), [N.stored_normalization_exists](EfficientFFA/Normalization.lean#L59). Output existence requires q ≤ B^n in addition to valid normalization parameters. Native stored-residue transport is included. Paper-facing endpoint: [Paper.normalization_exists](EfficientFFA/Paper.lean). |
| **L11** — [ffa.tex · accumulation bound](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L168) | L around B² permits about B additions; small constants can be handled lazily. | Refined | [Paper.accumulated_additions](EfficientFFA/Paper/Arithmetic.lean) bounds k additions from [lo,hi] by [lo,hi+k*(B−1)]; accumulated_within_limit supplies the signed-limit criterion. [Paper.scale_within_limit_of_div](EfficientFFA/Paper/Arithmetic.lean) proves that abs(c)≤L/B suffices for well-formed inputs. This is a uniform sufficient threshold, not a necessary condition for each input. Cost claims are excluded. |
| **L12** — [ffa.tex · normalization modulus reuse](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L165) | The multiplication auxiliary moduli also suffice for normalization in the reported settings. | Covered | Each [production parameter module](EfficientFFA/Instances/PaperParameters.lean) proves normalization_valid, same_moduli and normalize. The certificate table below gives explicit limits; all 0≤L≤limit are supported with fixed shifts/widths. The source leaves these values as a TODO. Normalization validity is checked independently of multiplication validity; no maximality claim is made. |

### Division and comparison

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **D01** — [ffa.tex · Division and comparisons](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L171) | Division is multiplication plus a nonzero condition; inversion is division of one. | Conditional | [D.inverse_exists_iff_coprime](EfficientFFA/Division.lean#L7), [D.division_iff](EfficientFFA/Division.lean#L18), [D.encoded_division_iff](EfficientFFA/Division.lean#L61), [D.encoded_inverse_iff](EfficientFFA/Division.lean#L69). For general q, the divisor must be a unit (coprime to q). Nonzero alone suffices only over a field. Section 3 allows composite q, so this qualification matters. |
| **D02** — [ffa.tex · Division and comparisons](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L171) | For prime q, an inverse of the difference exists iff the two residues differ. | Covered | [D.prime_inverse_iff](EfficientFFA/Division.lean#L34), [D.prime_disequality_iff](EfficientFFA/Division.lean#L55), [E.distinct_iff](EfficientFFA/Native/EllipticCurve.lean#L71). This is disequality, not an ordering comparison. Native EC disequality uses a combined inverse identity; the particular subtraction–normalization–multiplication circuit layout is not compiled. |

### Shifted representation

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **Z01** — [ffa.tex · sec:unique-zero](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L181) | When q ≤ B^n < 2q, shifted value 1+eval has a unique bounded zero encoding. | Covered | [S.value](EfficientFFA/ShiftedEncoding/Representation.lean#L6), [S.zero_iff_eval](EfficientFFA/ShiftedEncoding/Representation.lean#L9), [S.exists_unique_zero](EfficientFFA/ShiftedEncoding/Representation.lean#L27), [S.zero_iff_limbs](EfficientFFA/ShiftedEncoding/Representation.lean#L38). Zero is exactly the bounded limb representation of q−1; the capacity and strict upper bound are essential. |
| **Z02** — [ffa.tex · sec:unique-zero](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L181) | The shifted encoding still represents every foreign residue. | Covered | [S.exists_representation](EfficientFFA/ShiftedEncoding/Representation.lean#L51). Requires representational capacity and valid radix assumptions. |
| **Z03** — [ffa.tex · sec:unique-zero](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L181) | Zero testing reduces to checking the individual limbs against q−1. | Covered | [S.zero_iff_native_checks](EfficientFFA/ShiftedEncoding/Representation.lean#L63). In addition to q ≤ B^n < 2q, native equality needs B ≤ p to prevent limb aliasing. Cheapness in rows/copy constraints is not proved. |
| **Z04** — [ffa.tex · sec:unique-zero](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L181) | Shifted multiplication introduces the additional linear terms. | Covered | [SMB.shifted_product_identity](EfficientFFA/ShiftedEncoding/Multiplication/Definitions.lean#L16), [SMB.residual_mod](EfficientFFA/ShiftedEncoding/Multiplication/Definitions.lean#L22), [SMB.multiplication_iff_quotient](EfficientFFA/ShiftedEncoding/Multiplication/Definitions.lean#L32), [SM.residual_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L9), [SM.auxCore_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L25), [SM.nativeResidual_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L44), [SM.auxResidual_bounds](EfficientFFA/ShiftedEncoding/Multiplication/Bounds.lean#L54). Revised bounds and quotient parameters are used, not the unshifted bounds without adjustment. |
| **Z05** — [ffa.tex · sec:unique-zero](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L181) | The adapted shifted multiplication checks are sound and complete. | Covered | [SM.auxCore_congr](EfficientFFA/ShiftedEncoding/Multiplication/Soundness.lean#L8), [SM.multiplication_sound](EfficientFFA/ShiftedEncoding/Multiplication/Soundness.lean#L16), [SM.multiplication_complete](EfficientFFA/ShiftedEncoding/Multiplication/Completeness.lean#L54), [SM.accepts_iff_multiplication](EfficientFFA/ShiftedEncoding/Multiplication.lean#L7), [SM.multiplication_exists](EfficientFFA/ShiftedEncoding/Multiplication.lean#L17). Output existence additionally uses capacity; acceptance of a supplied triple uses its explicit bounds and shifted parameter conditions. |
| **Z06** — [ffa.tex · sec:unique-zero](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L181) | Normalization is unchanged because the two shifts cancel. | Covered | [S.value_congr_iff](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L112), [S.normalization_iff](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L116), [S.stored_normalization_sound](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L122), [S.stored_normalization_exists](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L131). The unshifted normalization checks preserve the shifted residue too. |
| **Z07** — [ffa.tex · sec:unique-zero](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ffa.tex#L181) | Adjust the least significant limb for shifted linear operations. | Covered | [S.eval_bump](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L16), [S.value_add](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L21), [S.value_sub](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L26), [S.value_neg](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L31), [S.value_add_constant](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L36), [S.value_scale](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L41), [S.bounded_add](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L56), [S.bounded_sub](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L61), [S.bounded_neg](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L66), [S.bounded_scale](EfficientFFA/ShiftedEncoding/Arithmetic.lean#L70). Addition uses +1, subtraction −1, negation −2, scaling +(c−1); corresponding signed bounds and native-representation lemmas are available. Nonempty limb vectors are needed for a low-limb correction. |

### EC identities and point representation

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **E01** — [ff-ecc.tex · sec:ffa-ecc](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L3) | Affine coordinates on a smooth short-Weierstrass curve describe actual elliptic-curve points. | Covered | [EC.Curve](EfficientFFA/EllipticCurve/Affine.lean#L10), [C.equation_iff](EfficientFFA/EllipticCurve/Affine.lean#L28), [C.nonsingular](EfficientFFA/EllipticCurve/Affine.lean#L31), [C.point](EfficientFFA/EllipticCurve/Affine.lean#L35), [C.point_ne_zero](EfficientFFA/EllipticCurve/Affine.lean#L38), [C.point_injective](EfficientFFA/EllipticCurve/Affine.lean#L41). The abstract field and smooth curve are explicit. Group semantics come from mathlib, rather than an assumed group law for arbitrary coordinates. |
| **E02** — [ff-ecc.tex · eq:curve-mem](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L102) | Membership uses a quadratic identity with an intermediate z=x². | Covered | [Native.GateKind.expression](EfficientFFA/Native/EllipticCurve.lean#L15), [E.onCurve_iff](EfficientFFA/Native/EllipticCurve.lean#L91). The native predicate checks both the square relation and the curve equation. An unlinked z is insufficient. |
| **E03** — [ff-ecc.tex · eq:lambda-slope](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L131) | The signed chord slope identities encode the line through P and ±Q. | Covered | [EC.chord](EfficientFFA/EllipticCurve/Affine.lean#L61), [EC.AddChecks](EfficientFFA/EllipticCurve/Affine.lean#L65), [EC.add_checks_iff](EfficientFFA/EllipticCurve/Affine.lean#L87), [E.add_iff](EfficientFFA/Native/EllipticCurve.lean#L108). The addition contract uses the appropriate signed equation. Identification with group addition requires valid inputs and distinct x-coordinates, unless that distinction is derived by a surrounding invariant. |
| **E04** — [ff-ecc.tex · eq:lambda-tangent](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L152) | The tangent equation defines doubling. | Conditional | [EC.tangent](EfficientFFA/EllipticCurve/Affine.lean#L62), [EC.DoubleChecks](EfficientFFA/EllipticCurve/Affine.lean#L70), [EC.double_checks_iff](EfficientFFA/EllipticCurve/Affine.lean#L103), [C.double_den_ne](EfficientFFA/EllipticCurve/GroupLaw.lean#L76), [E.double_iff](EfficientFFA/Native/EllipticCurve.lean#L123). Completeness for a finite affine result requires 2*y(P) ≠ 0. Soundness of accepted checks derives the needed nonzero denominator from smoothness. |
| **E05** — [ff-ecc.tex · eq:assert-lambda2](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L175) | The slope fixes x(R), and the linear relation fixes y(R). | Covered | [EC.result](EfficientFFA/EllipticCurve/Affine.lean#L58), [EC.output_determined](EfficientFFA/EllipticCurve/Affine.lean#L77), [C.result_group](EfficientFFA/EllipticCurve/GroupLaw.lean#L42), [C.addition_sound](EfficientFFA/EllipticCurve/GroupLaw.lean#L58), [C.doubling_sound](EfficientFFA/EllipticCurve/GroupLaw.lean#L87). No division by x(R)−x(P) is needed to determine y(R). The coordinate checks are connected to actual group addition. |
| **E06** — [ff-ecc.tex · sec:ecc-ids](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L62) | Encode the foreign identities over the native modulus using coefficient reduction and bounds. | Covered | [P.reduce_congr](EfficientFFA/Native/Polynomial.lean#L76), [P.eval_bounds](EfficientFFA/Native/Polynomial.lean#L103), [G.residual_congr](EfficientFFA/Native/Gate.lean#L69), [G.residual_bounds](EfficientFFA/Native/Gate.lean#L72), [G.auxCore_bounds](EfficientFFA/Native/Gate.lean#L76), [G.auxCore_congr](EfficientFFA/Native/Gate.lean#L86), [G.sound](EfficientFFA/Native/Gate.lean#L95), [G.accepts_iff](EfficientFFA/Native/Gate.lean#L177), [X.compile_eval](EfficientFFA/Native/Expression.lean#L57), [X.checks_iff](EfficientFFA/Native/Expression.lean#L107), [E.check_iff](EfficientFFA/Native/EllipticCurve.lean#L54). The sparse-polynomial/limb compiler is proved correct. Each gate kind requires valid arithmetic parameters, foreign modulus agreement, capacity and well-formed represented inputs. |
| **E07** — [ff-ecc.tex · sec:ecc-ids](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L62) | Replacing x³ by x*z reduces limb-product complexity from cubic to quadratic. | Excluded | [Native.GateKind.expression](EfficientFFA/Native/EllipticCurve.lean#L15), [X.compile_eval](EfficientFFA/Native/Expression.lean#L57). The linked quadratic templates are formalized. There is no separate asymptotic degree, monomial-count, row-count or cost theorem. |
| **E08** — [ff-ecc.tex · Boolean activation](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L178) | Boolean activation disables an identity at zero and enforces it at one. | Covered | [Native.bit_cases](EfficientFFA/Native/Activation.lean#L7), [G.Activated](EfficientFFA/Native/Activation.lean#L26), [G.activated_sound](EfficientFFA/Native/Activation.lean#L34), [G.activated_one](EfficientFFA/Native/Activation.lean#L46), [G.activated_zero](EfficientFFA/Native/Activation.lean#L51). The bit-root argument needs the native prime/field assumption; composite native rings can have extra idempotents. E.Check selects activation one. The new [E.CompleteConstraints](EfficientFFA/Native/CompleteCircuit.lean) instead constrains raw selector bits and equality tests, and derives branch activation polynomials; [E.completeConstraints_sound](EfficientFFA/Native/CompleteCircuit.lean) proves dispatch correctness. The existing whole-trace relation still uses logical dispatch. |
| **E09** — [ff-ecc.tex · shifted adaptation](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L74) | Adapt the EC identities to the unique-zero representation. | Covered | [X.compileShifted_eval](EfficientFFA/ShiftedEncoding/Expression.lean), shifted_residual_bounds, shifted_auxCore_bounds, shifted_witnesses_accept and shifted_checks_iff establish the shifted polynomial interpretation, bounds and native witnesses. [Native.ShiftedECEncoding](EfficientFFA/ShiftedEncoding/EllipticCurve.lean) proves membership, signed slope/tangent/output, equality, negation and nonzero identities, plus group-level addition/doubling soundness and completeness. Validity is for the shifted polynomials. Unique zero additionally requires B^n<2q. A small actual curve and the four-limb SECP256k1 setting (both native fields) discharge these arithmetic conditions. |
| **E10** — [ff-ecc.tex · Witnessing a point](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L198) | An infinity flag permits arbitrary coordinates for infinity; finite coordinates must be on the curve. | Covered | [EC.Encoded](EfficientFFA/EllipticCurve/Flagged.lean#L6), [C.Valid](EfficientFFA/EllipticCurve/Flagged.lean#L14), [C.decode](EfficientFFA/EllipticCurve/Flagged.lean#L16), [C.decode_finite](EfficientFFA/EllipticCurve/Flagged.lean#L19), [C.decode_infinity](EfficientFFA/EllipticCurve/Flagged.lean#L22), [E.flag_iff](EfficientFFA/Native/Trace.lean#L15). Lean Boolean tags have a native bit check. There is no standalone compiled implementation of the paper’s unified Valid gate or proof of its 2n+1-cell cost. Finite membership and tagged semantics are connected in the operation/trace contracts. |
| **E11** — [ff-ecc.tex · subgroup loading](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L221) | Check loaded points for subgroup membership, then preserve subgroup membership under operations. | Conditional | [SG.mem_iff_card_nsmul_eq_zero](EfficientFFA/EllipticCurve/Subgroup.lean#L8), [E.member_iff](EfficientFFA/Native/Subgroup.lean#L24), [C.trace_output_mem_subgroup](EfficientFFA/MSM/Subgroup.lean#L36), [E.trace_output_mem_subgroup](EfficientFFA/Native/Subgroup.lean#L12). The native membership predicate checks on-curve and [card H]P=0 via a complete-addition chain. Equivalence to membership in the chosen H requires coprimality of card H with the quotient order. Output closure needs subgroup inputs; prime subgroup order alone does not identify a subgroup when the cofactor shares that prime. |
| **E12** — [introduction.tex · contrib:ecc](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/introduction.tex#L98) | Dedicated identities avoid the cost of composing generic foreign-field operations. | Excluded | [E.add_iff](EfficientFFA/Native/EllipticCurve.lean#L108), [E.double_iff](EfficientFFA/Native/EllipticCurve.lean#L123). Correctness of the dedicated identities is proved. The stated naïve counts (including five subtractions, five normalizations and three multiplications) and comparative savings have no formal operation-cost theorem. |

### Point operations

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **O01** — [figures/double.tex · fig:double](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/double.tex#L28) | Doubling preserves the infinity flag and uses tangent/addition equations in the finite branch. | Conditional | [C.DoubleAccepts](EfficientFFA/EllipticCurve/Flagged.lean#L26), [C.flagged_double_sound](EfficientFFA/EllipticCurve/Flagged.lean#L35), [C.flagged_double_complete](EfficientFFA/EllipticCurve/Flagged.lean#L46), [C.flagged_double_witnesses_iff](EfficientFFA/EllipticCurve/Flagged.lean#L55), [C.flagged_double_complete_of_no_two_torsion](EfficientFFA/EllipticCurve/Flagged.lean#L91). Sound for accepted checks. Complete when the finite tangent denominator is nonzero; no nontrivial two-torsion is a sufficient group-level condition, consistent with the paper’s restriction. |
| **O02** — [ff-ecc.tex · doubling output explanation](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L250) | Excluding order three is used to justify the displayed doubling method. | Refined | [EC.output_determined](EfficientFFA/EllipticCurve/Affine.lean#L77), [C.flagged_double_witnesses_iff](EfficientFFA/EllipticCurve/Flagged.lean#L55). Lean does not need x(2P) ≠ x(P) or an order-three exclusion. The y-output is determined without dividing by that difference. The order-three regression in Tests/EllipticCurve.lean demonstrates this stronger coverage. |
| **O03** — [figures/incomplete-add.tex · fig:incomplete-add](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/incomplete-add.tex#L31) | Incomplete addition is sound and complete for valid finite inputs with distinct x. | Covered | [C.IncompleteAccepts](EfficientFFA/EllipticCurve/Flagged.lean#L30), [C.incomplete_sound](EfficientFFA/EllipticCurve/Flagged.lean#L62), [C.incomplete_complete](EfficientFFA/EllipticCurve/Flagged.lean#L70), [C.addition_sound](EfficientFFA/EllipticCurve/GroupLaw.lean#L58), [C.addition_complete](EfficientFFA/EllipticCurve/GroupLaw.lean#L65). The finite result and its curve membership are derived. Whether input validity/distinctness is separately checked or inherited is a surrounding-contract question. |
| **O04** — [figures/complete-add.tex · fig:complete-add](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/complete-add.tex#L35) | Complete addition handles identities, inverses, doubling and distinct inputs. | Refined | [C.CompleteAccepts](EfficientFFA/EllipticCurve/Complete.lean#L9), [C.complete_sound](EfficientFFA/EllipticCurve/Complete.lean#L21), [C.complete_exists](EfficientFFA/EllipticCurve/Complete.lean#L48), [C.complete_correct](EfficientFFA/EllipticCurve/Complete.lean#L76), [E.complete_iff](EfficientFFA/Native/Trace.lean#L47). Lean uses ordered branches. It proves complete addition, but not the literal conjunction of overlapping implications printed in fig:complete-add. It also handles order-two inputs by the inverse branch. [E.completeCircuit_iff](EfficientFFA/Native/CompleteCircuit.lean), [E.completeCircuit_sound](EfficientFFA/Native/CompleteCircuit.lean) and [E.completeCircuit_complete](EfficientFFA/Native/CompleteCircuit.lean) now establish a shared-limb, native-selector constraint realization. This needs native primality and, for exact copy soundness, B≤p, in addition to ECEncoding validity and valid inputs. The proposed fig:complete-add correction uses the ordered branches; it is not applied. Paper-facing endpoint: [Paper.complete_add_sound](EfficientFFA/Paper.lean). |
| **O05** — [figures/complete-add.tex · fig:complete-add](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/complete-add.tex#L35) | Copy the other input for an infinity input. | Refined | [EC.IdentityCopies](EfficientFFA/EllipticCurve/Flagged.lean#L104), [EC.identity_copies_iff](EfficientFFA/EllipticCurve/Flagged.lean#L108), [E.copy_iff](EfficientFFA/Native/EllipticCurve.lean#L82), [E.encodedCopy_iff](EfficientFFA/Native/Trace.lean#L22). The two literal copy implications require identical encodings when both inputs are infinity, which conflicts with arbitrary infinity coordinates. Ordered dispatch resolves this. Native copy predicates express equality of represented field values; literal equality of every limb of noncanonical encodings is a stronger contract. [E.copyLimbs_one_iff](EfficientFFA/Native/SharedGate.lean) proves that stronger native-copy contract when B≤p. CompleteCircuit uses it; completeness constructs canonical shared encodings. It does not promise to preserve arbitrary preassigned public limb encodings. Paper-facing endpoint: [Paper.native_complete_add_iff](EfficientFFA/Paper.lean). |
| **O06** — [figures/complete-add.tex · fig:complete-add](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/complete-add.tex#L35) | Coordinate-only inverse detection coexists with infinity-copy branches. | Refined | [Audit.single_infinity_literal_conflict](Tests/PaperAudit.lean#L10), [C.CompleteAccepts](EfficientFFA/EllipticCurve/Complete.lean#L9). The audit theorem refutes the literal simultaneous obligations when one input is infinity with coordinates −Q. Lean’s ordered branches resolve the overlap. fig:complete-add’s “incomplete” caption is also inconsistent with its surrounding complete-addition discussion. |
| **O07** — [figures/complete-add.tex · fig:complete-add](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/complete-add.tex#L35) | Copying is free and unique-zero comparison makes complete addition cheap. | Excluded | **No direct counterpart.** The shared-wire complete-add gadget has a selector/copy proof, but no row/copy/lookup cost model or PLONK layout compiler is present. Semantic equalities do not establish these resource claims. |

### MSM tables, traces and statistics

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **T01** — [figures/msm.tex · step:tables](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/msm.tex#L30) | Initialize offset tables so entry k represents kP−V, V=(b−1)U. | Covered | [MSM.entry](EfficientFFA/MSM/Tables.lean#L6), [MSM.entry_succ](EfficientFFA/MSM/Tables.lean#L8), [C.table_sound](EfficientFFA/MSM/Tables.lean#L68), [C.table_lookup_sound](EfficientFFA/MSM/Tables.lean#L185). Accepted raw table equations, on-curve base/start and the initial x-distinctness premise establish the group meaning of every table entry. |
| **T02** — [ff-ecc.tex · table construction](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L384) | The table recurrence implies internal validity/distinctness without extra per-entry guards. | Covered | [EC.x_ne_of_add_checks](EfficientFFA/MSM/Tables.lean#L28), [C.repeated_step](EfficientFFA/MSM/Tables.lean#L49), [C.table_guards](EfficientFFA/MSM/Tables.lean#L89), [C.table_sound](EfficientFFA/MSM/Tables.lean#L68), [C.table_safe](EfficientFFA/MSM/Tables.lean#L119). This is a soundness theorem about accepted table equations. Lean does not add per-entry guard constraints. |
| **T03** — [ff-ecc.tex · table construction](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L384) | Suitable offsets admit witnesses for all table equations. | Conditional | [MSM.TableSafe](EfficientFFA/MSM/Tables.lean#L14), [C.table_complete](EfficientFFA/MSM/Tables.lean#L142), [MSM.table_safe_iff_avoids](EfficientFFA/MSM/TableOffsets.lean#L24), [MSM.badOffsets_card_le](EfficientFFA/MSM/TableOffsets.lean#L61). The first x-distinctness check alone does not guarantee table witness existence (e.g. V=2P can fail later). This is handled by offset selection and rejection bounds, not by adding a new MSM guard. The recorded proposal restricts the paper’s guard implication to accepted table equations. |
| **T04** — [ff-ecc.tex · sec:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L327) | Select parameters giving safe table setup with few excluded seeds. | Conditional | [MSM.badSeeds_card_le](EfficientFFA/MSM/Parameters.lean#L25), [MSM.exists_safe_setup_prime](EfficientFFA/MSM/Parameters.lean#L79), [C.tables_exist_of_parameters](EfficientFFA/MSM/Parameters.lean#L101). Lean makes the paper’s qualitative claim quantitative: setup excludes at most 1+l*(b+1) seeds when steps=b−1 and the required scalar maps are injective. Existence requires this budget below group size. |
| **T05** — [figures/msm.tex · step:alpha](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/msm.tex#L26) | Tie supplied constants and table origins to a single random seed U. | Covered | [C.scale_sound](EfficientFFA/MSM/Chains.lean#L16), [C.scale_exists](EfficientFFA/MSM/Chains.lean#L47), [C.trace_setup](EfficientFFA/MSM/Trace.lean#L48), [E.scale_iff](EfficientFFA/Native/Trace.lean#L88), [E.trace_iff](EfficientFFA/Native/Trace.lean#L116). The trace verifies the scalar-multiplication links for V and the initial accumulator, rather than merely assuming unlinked constants. Complete-addition chains implement these links semantically; the particular cheap chain/circuit layout is not verified. |
| **T06** — [figures/msm.tex · table lookup](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/msm.tex#L43) | A bounded window selects its corresponding table entry. | Covered | [C.table_lookup_sound](EfficientFFA/MSM/Tables.lean#L185), [C.trace_lookup](EfficientFFA/MSM/Trace.lean#L58), [MSM.descending_range](EfficientFFA/MSM/TraceStatistics.lean#L6). Lookup selection is a mathematical relation with bounded indices, not a verification of the PLONK lookup argument or table layout. |
| **T07** — [ff-ecc.tex · sec:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L327) | Each window cancels its introduced offsets while retaining lU. | Covered | [MSM.addRows_eq](EfficientFFA/MSM/Loop.lean#L15), [MSM.loop_invariant](EfficientFFA/MSM/Loop.lean#L34), [MSM.row_invariant](EfficientFFA/MSM/Loop.lean#L89), [MSM.rowValue](EfficientFFA/MSM/Loop.lean#L82), [MSM.offsetCoeff](EfficientFFA/MSM/Loop.lean#L86), [C.trace_rows](EfficientFFA/MSM/Trace.lean#L96), [C.trace_boundaries](EfficientFFA/MSM/Trace.lean#L114). The row coefficient is b*l−(b−1)*j. The proof uses actual table identities and repeated doubling/addition relations. |
| **T08** — [figures/msm.tex · window traversal](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/msm.tex#L34) | The final accumulator represents the intended window expansion. | Refined | [MSM.horner_eq_sum](EfficientFFA/MSM/Loop.lean#L48), [MSM.descending](EfficientFFA/MSM/Loop.lean#L64), [MSM.loop_correct](EfficientFFA/MSM/Loop.lean#L68), [C.trace_sound_littleEndian](EfficientFFA/MSM/Trace.lean#L151), [E.trace_sound_littleEndian](EfficientFFA/Native/Trace.lean#L157). The printed expansion is little-endian but the printed Horner loop traverses forward. Lean traverses windows in descending order, producing Σ_i b^i*window(i,j). It does not verify the literal forward loop against that expansion. The corrected contract processes T down to 1. |
| **T09** — [figures/double.tex · fig:double](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/double.tex#L28) | Intermediate additions and doublings can use finite/incomplete operations. | Conditional | [MSM.addRows_ne_zero](EfficientFFA/MSM/Safety.lean#L7), [MSM.loop_ne_zero](EfficientFFA/MSM/Safety.lean#L19), [MSM.row_ready](EfficientFFA/MSM/Safety.lean#L37), [MSM.doubling_ready](EfficientFFA/MSM/Safety.lean#L57), [C.trace_complete](EfficientFFA/MSM/TraceCompleteness.lean#L162). Required nonidentity states follow from the accepted group execution and invertible radix map. The loop retains its printed x-distinctness check; table-internal guards remain derived. |
| **T10** — [figures/msm.tex · step:last-msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/msm.tex#L49) | Subtract lU and return the correct MSM, including a possible infinity output. | Covered | [C.trace_sound](EfficientFFA/MSM/Trace.lean#L134), [C.trace_sound_littleEndian](EfficientFFA/MSM/Trace.lean#L151), [E.trace_sound_littleEndian](EfficientFFA/Native/Trace.lean#L157). Applies to every accepted full trace with valid finite bases. The final subtraction uses complete addition. This includes native limb constraints under the ECEncoding contract. |
| **T11** — [ff-ecc.tex · sec:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L327) | Each potential loop collision excludes only a small number of seeds. | Conditional | [MSM.collision_iff](EfficientFFA/MSM/Collisions.lean#L29), [MSM.collision_coeff_bounds](EfficientFFA/MSM/Collisions.lean#L45), [MSM.collisionSeeds_card_le](EfficientFFA/MSM/Collisions.lean#L93), [MSM.loopBadSeeds_card_le_prime](EfficientFFA/MSM/Collisions.lean#L132). The two affine collision equations each exclude at most one seed when their scalar coefficients are injective. A sufficient prime-order condition is b*l+b−1 < N. |
| **T12** — [ff-ecc.tex · sec:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L327) | Uniform seed choice makes MSM witness failure unlikely. | Conditional | [MSM.failureBudget](EfficientFFA/MSM/Rejection.lean#L13), [MSM.uniform_group_failure_bound_prime](EfficientFFA/MSM/Rejection.lean#L125), [C.uniform_littleEndian_trace_failure_bound_prime](EfficientFFA/MSM/TraceStatistics.lean#L41), [E.uniform_littleEndian_failure_bound](EfficientFFA/Native/Statistics.lean#L21). For b=2^w, l bases, t windows and prime group order N with w,l>0 and b*l+b−1<N, failure probability is at most (1+l*(b+1)+2*t*l)/N. Bases/windows are fixed before uniform sampling. A negligible asymptotic bound additionally requires a suitable parameter family; no such asymptotic theorem is stated. |
| **T13** — [ff-ecc.tex · sec:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L327) | Successful abstract executions admit coordinate and native witnesses. | Covered | [C.trace_complete](EfficientFFA/MSM/TraceCompleteness.lean#L162), [C.TraceWitnesses](EfficientFFA/MSM/TraceCompleteness.lean#L63), [E.traceWitnesses_iff](EfficientFFA/Native/Statistics.lean#L13), [E.exists_correct_trace](EfficientFFA/Native/Statistics.lean#L34). The probability event is absence of any accepted trace, not failure of an unspecified runtime witness generator. Existence of a good seed additionally needs the failure budget below group order. |
| **T14** — [ff-ecc.tex · sec:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L327) | The MSM argument can operate inside a prime-order subgroup of a larger curve group. | Conditional | [MSM.groupAccepts_map_iff](EfficientFFA/MSM/Embedding.lean#L31), [C.trace_complete_subgroup](EfficientFFA/MSM/Subgroup.lean#L16), [E.uniform_subgroup_failure_bound](EfficientFFA/Native/Subgroup.lean#L38), [E.uniform_subgroup_failure_bound_checked](EfficientFFA/Native/Subgroup.lean#L67), [E.exists_correct_subgroup_trace](EfficientFFA/Native/Subgroup.lean#L50). Sample uniformly in H and use N=card H. The ambient group need not have prime order. Known subgroup membership suffices for the bound; using the native annihilation-based membership test additionally needs coprime cofactor. The sample includes zero, which is counted among excluded seeds. |
| **T15** — [ff-ecc.tex · sec:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L327) | GLV can further optimize the MSM and is used in the implementation. | Excluded | **No direct counterpart.** No GLV endomorphism, scalar decomposition, correctness theorem or cost comparison is present. |
| **T16** — [ff-ecc.tex · offset negation](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L391) | Negating y and preserving x/flag represents group negation. | Covered | [C.point_opposite](EfficientFFA/MSM/Tables.lean#L204), [C.coordinates_neg](EfficientFFA/MSM/TraceCompleteness.lean#L33), [E.opposite_iff](EfficientFFA/Native/Trace.lean#L28). The native opposite relation links the encoded constants used for table starts and the final correction. |
| **T17** — [ff-ecc.tex · thm:msm](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/ff-ecc.tex#L404) | MSM soundness and statistical completeness, with the source’s bound TODO. | Conditional | [Paper.msm_sound](EfficientFFA/Paper.lean), [Paper.msm_failure_bound](EfficientFFA/Paper.lean), [Paper.msm_subgroup_failure_bound](EfficientFFA/Paper.lean), [Paper.msm_exists_correct](EfficientFFA/Paper.lean) and [Paper.msm_exists_correct_subgroup](EfficientFFA/Paper.lean). The explicit budget is 1+l*(2^w+1)+2*t*l. Requires the corrected traversal/complete addition; statistical hypotheses and the stronger existence condition are listed in the corrected contracts below. [Paper.msm_contract](EfficientFFA/Paper/MSMContract.lean) and msm_subgroup_contract consolidate these outcomes without adding per-entry table guards. The printed theorem has not been edited. |

### Context and prior-work claims

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **B01** — [introduction.tex · sec:related](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/introduction.tex#L250) | SNARK/PLONK security, succinctness, setup, recursion, cycles, lookup/permutation arguments and cited applications. | Excluded | **No direct counterpart.** These are cited foundations and motivation, not results proved by this arithmetic library. No reduction establishes knowledge soundness or zero knowledge of a PLONK proof system. Bibliographic assertions are grouped here, not counted as new paper theorems. |
| **B02** — [introduction.tex · contrib:mul](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/introduction.tex#L82) | Weighted bounds enable deterministic reconstruction with favorable auxiliary moduli. | Covered | [Paper.tight_single_le_loose](EfficientFFA/Paper/Arithmetic.lean) and [Paper.tight_double_le_loose](EfficientFFA/Paper/Arithmetic.lean) prove the non-strict comparison to count-times-(q−1) bounds. [Production certificates](EfficientFFA/Instances/PaperParameters.lean) establish sufficiency of the reported auxiliary moduli. No strict improvement, optimal modulus count or efficiency comparison is claimed universally. |
| **B03** — [introduction.tex · contrib:impl](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/introduction.tex#L161) | Emulation overhead is about one order of magnitude and enables efficient arbitrary-curve applications. | Excluded | **No direct counterpart.** These are implementation/benchmark conclusions, not consequences of the arithmetic acceptance equivalences alone. |

### Verification and implementation assertions

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **I01** — [introduction.tex · contrib:fv](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/introduction.tex#L122) | Machine-checked correctness of the stated arithmetic and EC/MSM theory. | Excluded | Attribution, novelty and historical tool/version assertions are not mathematical proof obligations in this Lean-only inventory. The actual mathematical coverage is recorded in M, L, Z, E, O and T rows, and theorem trust is checked by the build. No other formalization counts as evidence. |
| **I02** — [benches.tex · sec:benches](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/benches.tex#L3) | Reported PLONK row/column/degree/lookup architecture. | Excluded | The current source reports at most three rows, degree at most five and four parallel lookups of at most sixteen bits. Layout, lookup and permutation implementations are outside this theoretical coverage milestone. |
| **I03** — [introduction.tex · contrib:impl](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/introduction.tex#L161) | The implementation is parametric over emulated/parent curves and supports blockchain precompiles. | Excluded | [Native.ECEncoding](EfficientFFA/Native/EllipticCurve.lean#L28). Lean is parameterized over a prime foreign field and an explicit valid encoding. This does not prove compatibility of the Halo2 implementation with Ethereum/Cardano/Solana or a deployed verifier. |

### Concrete parameter claims and excluded applications

| ID and current source | Claim | Status | Lean statements and correspondence boundary |
|---|---|---|---|
| **P01** — [figures/limbs-table.tex · tab:emulation-params](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/limbs-table.tex#L10) | Arithmetic sufficiency of the three-limb SECP256k1 configuration. | Covered | [PaperParameters.secp3](EfficientFFA/Instances/PaperParameters/Secp3.lean): multiplication_valid, ec_valid (all nine identities), capacity and radix_headroom, for both native scalar moduli. See exact witness widths below. The conditional encoding constructor connects these certificates to ECEncoding. Costs and cryptographic group-order/primality proofs are not asserted. |
| **P02** — [figures/limbs-table.tex · tab:emulation-params](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/limbs-table.tex#L10) | Arithmetic sufficiency of the four-limb SECP256k1 configuration. | Covered | [PaperParameters.secp4](EfficientFFA/Instances/PaperParameters/Secp4.lean): multiplication_valid, ec_valid (all nine identities), capacity and radix_headroom, for both native scalar moduli. See exact witness widths below. The conditional encoding constructor connects these certificates to ECEncoding. Costs and cryptographic group-order/primality proofs are not asserted. |
| **P03** — [figures/limbs-table.tex · tab:emulation-params](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/limbs-table.tex#L10) | Arithmetic sufficiency of the five-limb SECP256k1 configuration. | Covered | [PaperParameters.secp5](EfficientFFA/Instances/PaperParameters/Secp5.lean): multiplication_valid, ec_valid (all nine identities), capacity and radix_headroom, for both native scalar moduli. See exact witness widths below. The conditional encoding constructor connects these certificates to ECEncoding. Costs and cryptographic group-order/primality proofs are not asserted. |
| **P04** — [figures/limbs-table.tex · tab:emulation-params](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/limbs-table.tex#L10) | Arithmetic sufficiency of the six-limb SECP256k1 configuration. | Covered | [PaperParameters.secp6](EfficientFFA/Instances/PaperParameters/Secp6.lean): multiplication_valid, ec_valid (all nine identities), capacity and radix_headroom, for both native scalar moduli. See exact witness widths below. The conditional encoding constructor connects these certificates to ECEncoding. Costs and cryptographic group-order/primality proofs are not asserted. |
| **P05** — [figures/limbs-table.tex · tab:emulation-params](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/figures/limbs-table.tex#L10) | Comparison of the most efficient row/cell configurations. | Excluded | The current source distinguishes a four-limb nine-column row optimum from a four-limb five-column cell optimum. These implementation cost claims are outside the mathematical coverage target. |
| **P06** — [appendix.tex · app:ecdsa](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/appendix.tex#L283) | ECDSA signing/verification equations and their implementation. | Excluded | **No direct counterpart.** No ECDSA correctness/security theorem or verification-circuit specification is present. MSM correctness alone does not certify this application, its inversions, scalar reductions or exceptional cases. |
| **P07** — [benches.tex · sec:ecdsa-comparison](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/benches.tex#L82) | Prove knowledge of t distinct valid signatures with keys in raw S or Poseidon-committed S. | Excluded | **No direct counterpart.** Neither application relation, membership/distinctness composition, Poseidon commitment nor proof-of-knowledge property is formalized. |
| **P08** — [benches.tex · sec:ecdsa-comparison](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/benches.tex#L82) | Application timings, scaling and benchmark comparisons. | Excluded | Measurements and empirical explanations are outside this milestone. Existing mathematical MSM theorems do not certify application benchmarks. |
| **P09** — [benches.tex · self-recursion](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/benches.tex#L201) | Self-recursive PLONK verification uses accumulation to defer KZG pairings. | Excluded | **No direct counterpart.** No PLONK verifier, accumulation scheme, pairing deferral, counter application or recursive composition theorem is formalized here. |
| **P10** — [benches.tex · self-recursion](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/benches.tex#L201) | Arithmetic sufficiency of the self-emulation parameter sets. | Covered | [PaperParameters.blsSelf](EfficientFFA/Instances/PaperParameters/BlsSelf.lean) and [PaperParameters.bnSelf](EfficientFFA/Instances/PaperParameters/BnSelf.lean) prove multiplication_valid, ec_valid (all nine identities), capacity and radix_headroom for the exact reported self-emulation moduli. These are deterministic arithmetic certificates; recursive-proof correctness, costs and group orders remain separate. |
| **P11** — [benches.tex · self-recursion](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/benches.tex#L201) | Reported self-recursion proof sizes, times and circuit sizes. | Excluded | These measurements have changed since the older PDF. They are deliberately not copied into a mathematical proof inventory or treated as Lean claims. |
| **P12** — [benches.tex · self-recursion](https://github.com/miguel-ambrona/ffa-paper/blob/a811ec79ffd29008ee72c1b0c927ba1414599758/benches.tex#L201) | Foreign-field self-recursion is simpler/less error-prone than cycle-based approaches and suitable for fixed proving systems. | Excluded | **No direct counterpart.** This is a qualitative engineering assessment, not a formal comparative reliability result. |

## Checked arithmetic certificates (step 4)

The six modules under [Instances/PaperParameters](EfficientFFA/Instances/PaperParameters.lean)
cover ten settings: each SECP256k1 row is proved for **both** BN254 and
BLS12-381 native scalar moduli; each self-emulation row uses its own native
scalar modulus. The exact foreign/native integers are fixed in
[Constants.lean](EfficientFFA/Instances/PaperParameters/Constants.lean), with
primary-source references. The foreign modulus is the named curve's **base**
field modulus, distinct from the native scalar modulus.

Each row proves multiplication Valid, all nine compiled EC identity Valid
conditions, capacity q≤B^n, native headroom B²<p, normalization Valid and
literal equality of the reused modulus lists. EC widths are shared across
all nine identities. All numerical inequalities use kernel-checked decide;
no external calculator result is trusted by Lean.

| Configuration | Multiplication (t; tm) | Shared EC (t; tm) | Supported normalization limit | Normalization (t; tm) |
|---|---|---|---|---|
| SECP256k1, n=3, B=2^86 | 90; (122,122) | 92; (124,124) | 0≤L≤2^248 | 166; (167,166) |
| SECP256k1, n=4, B=2^64 | 67; (98) | 69; (100) | 0≤L≤2^186 | 124; (125) |
| SECP256k1, n=5, B=2^52 | 59; (90) | 61; (92) | 0≤L≤2^142 | 96; (97) |
| SECP256k1, n=6, B=2^44 | 55; (67) | 57; (70) | 0≤L≤2^114 | 80; (81) |
| BLS12-381 self-emulation, n=7, B=2^56 | 115; (116,116) | 117; (118,118) | 0≤L≤2^140 | 97; (118,118) |
| BN254 self-emulation, n=6, B=2^52 | 108; (108) | 109; (110) | 0≤L≤2^111 | 112; (111) |

Here tm entries follow the auxiliary-modulus order printed in the paper.
The normalization certificate fixes its limit at the displayed maximum.
Paper.normalization_input_mono transports every smaller signed input interval
to that **same** certificate; it does not recompute shifts for each L.
Each module's normalize theorem constructs an output and witnesses for such
an input, and normalization_valid supplies soundness via the general
normalization equivalence. These are sufficient limits, not maximality or
minimal-witness-width theorems.

The encoding constructors accept a prime foreign field, a smooth curve with
the stated coefficients and equality to the certified foreign modulus. They
then discharge the ECEncoding arithmetic obligations. They do not prove
large-field primality, curve/subgroup cardinalities, MSM parameter-size
conditions, native primality for the separate selector gadget, or PLONK
implementation correspondence.

## Shifted identities and their parameter boundary (step 5)

[ShiftedEncoding/Expression.lean](EfficientFFA/ShiftedEncoding/Expression.lean)
substitutes 1+x for every variable and then compiles an actual sparse limb
polynomial. Its evaluation theorem identifies the result with the existing
shifted interpretation. Bounds and quotient witnesses are obtained for this
new polynomial, including every extra constant and linear term. The proof
does not assume that ordinary polynomial validity transfers automatically.

[ShiftedEncoding/EllipticCurve.lean](EfficientFFA/ShiftedEncoding/EllipticCurve.lean)
instantiates all nine identity kinds, checks the square linkage for membership,
and reuses the existing coordinate/group results. The finite doubling witness
condition remains exactly 2*y(P)≠0; soundness needs no added denominator guard.
The check_iff_ordinary theorem identifies the represented coordinate relation
for independently valid ordinary and shifted encodings, even with different
limb counts or moduli. This is an identity-level result; the paper's MSM uses
the ordinary encoding and its existing trace contracts.

[Instances/ShiftedCurve17.lean](EfficientFFA/Instances/ShiftedCurve17.lean)
checks all shifted numerical obligations on the actual 17-element-field curve.
[Instances/PaperParameters/ShiftedSecp4.lean](EfficientFFA/Instances/PaperParameters/ShiftedSecp4.lean)
rechecks the four-limb SECP256k1 configuration over both native fields: the
existing shared EC widths (69;100) also satisfy the shifted bounds. Both
instances satisfy the separate B^n<2q condition for unique zero. Shifted
arithmetic needs only q≤B^n for representation; unique zero must not be inferred
from it. No blanket unique-zero assertion is made for the other table rows.

Tests/ShiftedEC.lean checks actual supplied slope limbs and explicit quotient
witnesses, and shows that forgetting the shift makes that same assignment
fail the ordinary slope identity. It also checks finite addition/doubling
and distinguishes all-zero limbs (value one) from the zero encoding.

## Theoretical proof queue

Steps 1–7 are complete for the agreed theoretical scope: inventory, corrected
contracts, interfaces, arithmetic correspondence, shifted EC identities,
consolidated MSM contracts and the final audit below. The following table
preserves gap IDs and their resolution evidence. The paper remains unchanged.

| Gap | Claim IDs | Status and evidence / remaining work |
|---|---|---|
| G01 — concrete arithmetic parameters | P01–P04, P10; numerical part of B02 | Closed: all ten settings have multiplication/EC Valid and capacity certificates above. Cryptographic primality/group-order facts are explicitly outside these integer certificates. |
| G02 — normalization modulus reuse | L12 | Closed: per-setting normalization_valid, same_moduli and normalize, with the explicit supported L intervals above. |
| G03 — quotient-rounding correspondence | M04, M10–M12 | Closed: Paper.lower_trunc_eq, floor_width_of_trunc and multiplication_valid_of_trunc in Paper/Rounding.lean; corresponding normalization/native bridges are also proved. NoWrap must be proved at the actual chosen widths. |
| G04 — shifted EC identities | E09 | Closed: Expression.compileShifted_eval, shifted_residual_bounds, shifted_auxCore_bounds, shifted_witnesses_accept and shifted_checks_iff; ShiftedECEncoding.onCurve_iff, add_iff, double_iff, addition_sound/complete and doubling_sound/complete. Independent numeric checks cover the small curve and four-limb SECP256k1 over both native fields. |
| G05 — duplicate residue representations | F04 | Closed: Paper.residue_injective and duplicate_residues_iff classify the positive-q/capacity boundary, including equality. |
| G06 — accumulation and constant bounds | L11 | Closed: Paper.accumulated_additions, accumulated_within_limit, scale_within_limit and scale_within_limit_of_div specify initial intervals, counts and sufficient signed scaling bounds. |
| G07 — comparison of arithmetic bounds | B02 | Closed: Paper.tight_single_le_loose and tight_double_le_loose prove the universal non-strict comparison. The concrete certificates establish sufficiency, not universal strict savings or optimality. |

Excluded items do not become obligations just because they have mathematical
notation: ECDSA/security protocols, recursion, GLV implementation, PLONK layout
and application performance are uses or external background, not the FFA/EC/MSM
arithmetic theory selected for this milestone. Paper statements depending on
such uses must remain clearly identified as outside the theorem contracts.

## Final correspondence audit (steps 6–7)

**Verdict:** no Open or Partial rows remain in this agreed inventory. This is
coverage of the corrected mathematical contracts and their explicit hypotheses,
not certification of the literal unedited paper or a deployed circuit.
The 92 claim families are: 56 Covered, 9 Refined, 11 Conditional and 16 Excluded.
These statuses are qualitative; they are not a theorem count or coverage score.

The four theorem environments in the pinned source were rechecked:

| Source label | Final Lean endpoint | Audit conclusion |
|---|---|---|
| thm:mul | Paper.multiplication_iff | Supplied bounded triples; Valid arithmetic conditions, with the rounding bridge proved. |
| thm:mul-soundness | Paper.multiplication_sound | Positivity and no-wrap suffice; neither width adequacy nor output capacity is needed for this direction. |
| thm:mul-completeness | Paper.multiplication_complete | Positivity and witness widths suffice; construction of an arbitrary output separately needs capacity. |
| thm:msm | Paper.msm_contract / msm_subgroup_contract | Corrected traversal and ordered final addition; fixed inputs and uniform sampling; explicit group-size and arithmetic conditions. |

The MSM contracts keep the layers separate: every accepted linked trace is
sound; random-seed failure is bounded by (1+l*(2^w+1)+2*t*l)/N; a correct
trace is guaranteed to exist when that numerator is strictly below N. The
sampling space includes zero. The figure's input windows are nonnegative and
bounded, so the sum is their finite little-endian expansion; there is no claim
about an unspecified preprocessing of arbitrary signed scalars. Input base
functions are required valid also at unused indices; a finite nonempty input
can be extended by repeating its first valid base. No extra table-internal
x-distinctness checks were introduced.

The arithmetic certificates discharge integer inequalities for the exact
reported moduli. Cryptographic field primality, smoothness and group/subgroup
orders remain explicit inputs to concrete-curve applications. The checked
small curve supplies a nonvacuous full instance. The shifted certificates
establish the optional identity adaptation; they do not silently replace the
ordinary encoding used by the MSM trace.

Remaining paper work is the C01–C08 correction register, not an open Lean
proof queue: fix the window order and complete-add branches; state table
soundness separately from offset witness existence; qualify division and
finite doubling; fix indices/scaling wording; explain rounding compatibility;
and insert the probability contract, parameter conditions and normalization
limits. A claim of asymptotic negligibility still needs a specified parameter
family; the checked contract gives the explicit finite bound. Implementation,
PLONK layout, GLV and applications retain their stated exclusions.

## Validation, provenance and maintenance

Validation on 2026-11-12: `lake build` passed (8650 jobs); 368 distinct
declaration references resolved and all 477 library theorem dependency reports
contained only propext, Classical.choice and Quot.sound (or a subset).

The default build includes the interface, the existing regressions and
Tests/PaperCorrespondence.lean. It checks all referenced declarations and
prints the axiom dependencies of the headline, combined MSM and new shifted
theorems. The wrappers reuse
existing acceptance definitions and proofs; they introduce no project axioms,
admissions, new branch assumptions or extra per-entry table constraints.
The original library had 364 theorem reports; 14 headline wrappers, 69 arithmetic
results and 30 shifted/combined-contract results bring that to 477. Eight
additional reports check encoding constructors.

Every displayed source anchor was checked against the pinned local LaTeX.
The reference checks are not an automated proof of prose equivalence or source
inventory completeness. Production numerical validity is established by the
separate compiled certificates, not by resolving declaration names. A change in paper
commit requires reviewing the affected claim contracts, not just renumbering
links. No external Lean artifact or archive was consulted.

PAPER_AUDIT.md preserves the earlier historical audit. The original 13-page
PDF remains identified by SHA-256
`c075bb9c3db566eb579495e64eb074c2783cdba34dcd1417132eb5756e7b36dd`;
it is not the current source for claim locations or theorem numbering. The
old input-output-hk paper checkout and its unapplied proposal record were
preserved when switching to Miguel's repository. They are historical material,
not the source of this specification. This work makes no edits to the paper.
