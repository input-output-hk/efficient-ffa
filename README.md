# Efficient Foreign-Field Arithmetic in PLONK
Formalization of proofs for efficient foreign field arithmetic (FFA) and multi-scalar multiplication (MSM) algorithms developed at IOG/Midnight.

See more in the associated [paper](https://eprint.iacr.org/2025/695).

## Requirements

```
EASYCRYPT_REVISION =  a214a56
JASMIN_VERSION     =  2023.06.1
ALT-ERGO           >= v2.5.1
CVC4               >= 1.8
Z3                 >= 4.8.7
```

## Contents
* `FFA_soundness.ec` the proof that whenever the system of constraints is satisfied then we have correctly multipled foreign field elements.
* `FFA_completeness.ec` the converse of the above.
* `FFA.ec` some common definitions.
* `MultiScalarMul_Abstract_Setup.ec` abstract setup for MSM algorithms.
* `MultiScalarMul_Abstract.ec` correctness of unoptimized (perfect) MSM algorithm.
* `MultiScalarMul_Abstract_Completeness.ec` statistical completeness of optimized MSM.
* `MultiScalarMul_Abstract_Soundness.ec` perfect soundness of optimized MSM.


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
divisibility lemma also have proofs. There are no active admissions in the
six local files checked below. The scalar-window comment now says
**big-endian**, matching the existing specification and forward loop.

### Reproducing the checks

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
The script checks every local file in the MSM dependency chain as a
top-level file, plus acceptance regression lemmas. It then requires both
deliberately invalid theorems in `tests/*MustFail.ec` to be rejected.
In temporary copies restoring the corresponding original declaration,
each negative test successfully proved `false`; both fail after repair.
These tests detect the two known contradictions, not arbitrary
inconsistency.

A separate `-check-all` attempt, which also rechecks EasyCrypt's standard
library, failed in that library's `List.ec` at line 2687 before reaching
the project. The local check script therefore uses the standard library
as supplied. The checker warns about the OCaml 5.2.1 garbage collector.

### Remaining scope

- Group, coordinate, scalar-inversion, distribution and parameter
  assumptions remain explicit axioms. This repair does not establish a
  model of every remaining axiom or instantiate a concrete elliptic curve.
- `perfect_table_pure` still uses total mathematical group operations.
  Construction of this table with incomplete additions is not verified;
  the table-construction counterexample discussed in the paper review
  still needs a separate precondition and proof.
- The completeness bound is still
  `p2 P s + T * l * (p1 + p1)`, where `p2` is the rejection probability
  of the newly defined admissibility condition. No small numerical bound
  on `p2` is proved here. Invalid scalar windows force rejection.
- The separate FFA/Jasmin proofs have not been checked with this newer
  toolchain, and the paper and Lean artifact are unchanged.
