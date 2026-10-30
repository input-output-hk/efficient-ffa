# Repository migration record

Date: 2026-10-30.

The combined repository keeps each formalization independently buildable and
adds shared navigation and paper coverage documentation. The mathematical
sources, theorem statements and dependency versions are unchanged by the move.
The paper source repository remains separate.

## Source histories

| Development | Source repository | Imported commit |
|---|---|---|
| EasyCrypt | input-output-hk/efficient-ffa | `65025da593fb569568871404004716c2a4ea5a16` |
| Lean | dfirsov/efficient-ffa-lean | `27dc1eae1edfdfa00864280da109ffbe801d1320` |

The Lean source commit first records the previously pending paper-to-Lean map
and its checked declaration index. That source commit passed `lake build`
before import.

EasyCrypt was moved under easycrypt/ in commit `6fc9b40`. Lean was imported
under lean/ with a non-squashed Git subtree merge in commit
`ed435b75d6917954681e12db9fe02a055cbcd1ed`. Both source commits are ancestors of the combined branch;
no history rewrite or Git submodule is involved.

The imported tree identities were checked before documentation updates:

| Artifact | Source tree and matching imported subtree |
|---|---|
| EasyCrypt | `49f861cecdb1d7d4db1914cd04aad4b0dd4f2dcb` |
| Lean | `5d3dcedbfa49b6be70da2f9fb6349856ffa40f67` |

The existing `sound-and-complete-ffa` tag retains object
`57a91417648a1d617c97f86a778e02e58eca7446`. It still names the historical
release and does not acquire the new directory structure or later proofs.

## Layout changes

- EasyCrypt retains its existing relative source layout inside easycrypt/.
  Its check and packaging scripts resolve paths relative to their own location.
- Lean retains its package layout, toolchain pins, mathlib manifest, tests,
  detailed paper map and scoped agent instructions inside lean/.
- The top-level README describes both build commands and their trust boundaries.
  docs/coverage.md links principal corresponding results and records differences
  in hypotheses and scope. The detailed 89-entry map remains under lean/.
- Language README introductions and agent guidance were updated for the shared
  repository. The independent Lean source policy is preserved. No external
  supplied Lean artifact or archive was consulted.
- The old EasyCrypt paper/ directory remains as easycrypt/paper/ because it holds
  a historical patch proposal, not the paper source repository.

The migration was prepared in a separate working tree so that the original
EasyCrypt and Lean checkouts remained available during validation. Future
proof changes can be made directly in the combined directories. Avoid parallel
maintenance of independent copies after adopting the combined repository.

## Validation

- The moved Lean project passes `lake build`, including Tests and all 236
  declaration references in Tests/PaperCorrespondence.lean.
- All 319 library theorem axiom reports use only the standard Lean axioms
  (or none). Cached mathlib artifacts were reused; the standard library was not
  rebuilt from scratch.
- The moved EasyCrypt project passes the full strict check: 32 root theories
  and 26 regressions, including all 14 expected proof rejections. Generated
  package consistency and the 58-file proof-policy check also pass.
- Source-tree identity and ancestor checks confirm preservation of both imported
  developments. Historical release-tag identity is unchanged.

For EasyCrypt validation, the recorded checker revision was rebuilt in a
separate temporary tool directory using the existing OCaml/Why3/Alt-Ergo
installation. Z3 4.8.12 was unpacked into that temporary environment and both
solvers registered in a temporary Why3 configuration. No system installation,
user solver configuration, project toolchain pin or proof was changed. The
supplied EasyCrypt standard library remains trusted, as in the original checks.

CI, production instances, paper revisions and circuit/benchmark verification
were not added by this migration.
