# Efficient Foreign-Field Arithmetic in PLONK
Formalization of soundness and correctness proofs of efficient foreign field arithmetic (FFA) developed  at IOG/Midnight.

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

