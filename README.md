# Efficient Foreign-Field Arithmetic in PLONK

This repository contains two independently developed formalizations of the
arithmetic and elliptic-curve/MSM results in
[Efficient Foreign-Field Arithmetic in PLONK](https://eprint.iacr.org/2025/695).
The developments share a mathematical subject and coverage documentation;
each has its own definitions, assumptions, toolchain and proof checks.

| Directory | Contents | Start here |
|---|---|---|
| [easycrypt/](easycrypt/) | EasyCrypt arithmetic, probabilistic MSM programs, coordinate constraints and small concrete instances | [Build instructions and status](easycrypt/README.md) |
| [lean/](lean/) | Independent Lean/mathlib arithmetic, EC group semantics, native encodings, MSM traces and subgroup support | [Build instructions and source policy](lean/README.md) |
| [docs/](docs/) | Cross-language coverage and repository provenance | [Paper coverage](docs/coverage.md), [migration record](docs/MIGRATION.md) |

Both directories contain their sources directly. A normal clone obtains both
formalizations; no Git submodules or sibling checkout is required. The paper
sources remain in the separate [ffa-paper repository](https://github.com/miguel-ambrona/ffa-paper).

## Checking the formalizations

Run these from the repository root after installing the respective toolchains.
Each command can also be run independently from its language directory.

### Lean

Lean and mathlib versions are pinned by [lean/lean-toolchain](lean/lean-toolchain)
and [lean/lake-manifest.json](lean/lake-manifest.json). On a fresh checkout,
fetch the mathlib cache, then build the library and regression suite:

~~~bash
(cd lean && lake exe cache get)
(cd lean && lake build)
~~~

The default build includes the paper declaration-reference index. See
[lean/README.md](lean/README.md) for the axiom reports and trust boundary.

### EasyCrypt

Install the versions recorded in [easycrypt/toolchain.json](easycrypt/toolchain.json),
including Why3 with Alt-Ergo and Z3 registered, then run:

~~~bash
EASYCRYPT=/path/to/easycrypt ./easycrypt/scripts/check-local.sh -why3 /path/to/why3.conf
~~~

The script resolves its source directory relative to itself. It checks every
local theory, positive regressions, expected proof failures, generated-package
consistency and the proof policy. The supplied EasyCrypt standard library is
trusted rather than rebuilt. The shorter MSM-only script is not a substitute
for this complete check.

## Scope and correspondence

The [shared coverage guide](docs/coverage.md) links the two numbered
multiplication theorems and the principal EC/MSM results in both languages.
The [detailed Lean inventory](lean/PAPER_RESULTS_MAP.md) also records prose,
algorithm and application claims with no formal counterpart.

The formalizations use documented corrections to the printed complete-addition
branches and MSM window traversal. Corresponding theorem names do not establish
cross-language equivalence. Generic parameter assumptions and representation
boundaries remain part of the results; consult the linked statements.

The current Lean-only theoretical inventory covers all reported arithmetic
parameter settings, normalization modulus reuse and shifted EC identities.
Its [final correspondence audit](lean/PAPER_RESULTS_MAP.md) records the
explicit hypotheses and paper corrections needed for that coverage claim.
CI, circuit implementation correspondence and benchmark/application
verification remain outside this scope. Historical
release tags keep their original contents; they are not labels for the current
combined tree.
