# Efficient Foreign-Field Arithmetic in PLONK
Formalization of proofs for efficient foreign field arithmetic (FFA) and multi-scalar multiplication (MSM) algorithms developed at IOG/Midnight.

See more in the associated [paper](https://eprint.iacr.org/2025/695).

## Toolchain and checks

The validated versions are recorded in [toolchain.json](toolchain.json).
Install those tools, register Alt-Ergo and Z3 with Why3, then run:

```bash
EASYCRYPT=/path/to/easycrypt ./scripts/check-local.sh -why3 /path/to/why3.conf
```

The script checks all 13 retained local theories independently, including
all FFA dependencies, then the positive and negative regression files.
It rejects explicit admissions and weak/report proof modes, accounting for
nested comments. Standard-library proofs are trusted as supplied rather
than rechecked. Python 3 and Bash are needed for the check scripts.

The toolchain manifest records tested versions; automated environment
provisioning and CI integration remain to be added. The original upstream
requirements were EasyCrypt a214a56, Jasmin 2023.06.1, Alt-Ergo >= 2.5.1,
CVC4 >= 1.8 and Z3 >= 4.8.7. The current scripts target the newer recorded
EasyCrypt revision.

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
- All retained local FFA dependencies and theorem files now check directly
  with the recorded toolchain. This establishes the proofs under their
  stated assumptions; concrete field parameters and circuit composition
  remain open. The paper and Lean artifact are unchanged.

## Audit cleanup and next steps

Unused `WhileApprox.eca`, `JWord_array.ec` and the processor-specific portion
of `JWord.ec` have been removed. The generic word theory and limb arithmetic
needed by FFA remain. This removes an unsound admitted loop bound and an
incorrect SIMD comparison from code outside the FFA/MSM dependency paths.

See [the formalization repair plan](FORMALIZATION_REPAIR_PLAN.md) for the
validation status and concrete steps covering distribution normalization,
table construction, rejection bounds and concrete curve/field instances.

## Sampler normalization repair

The abstract random-point distribution now explicitly assumes
`is_lossless r_distr`. Full support and uniform point masses alone do not
imply normalization. `tests/DistributionSemantics.ec` proves that a half-mass
singleton distribution is full and uniform but not lossless;
`tests/NonLosslessSamplerMustFail.ec` must fail to prove its sampler lossless.

The completeness theory proves `UniformU_lossless`, instantiates soundness
as `MSM_uniform_soundness`, and proves termination of the corresponding MSM
run as `MSM_uniform_lossless`. The new `MSM_uniform_success` theorem gives:

```text
Pr[MultiScalarMul(UniformU).run(P,s) returns an accepted result]
  >= 1 - (p2 P s + 2*T*l*p1).
```

This is a conditional abstract guarantee. Normalization still needs to be
discharged by a concrete finite sampler; `p2` remains unbounded, and table
construction remains idealized. In particular, this is not yet a small
numerical failure bound for the implemented circuit.
