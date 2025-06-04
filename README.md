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

