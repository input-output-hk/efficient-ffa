# Working on the combined formalization repository

- Keep EasyCrypt sources, tests and toolchain files under easycrypt/; keep Lean
  sources, tests and toolchain files under lean/. Each project must build on its own.
- Read the relevant language README and lean/AGENTS.md before changing proofs.
- Maintain docs/coverage.md when a result's coverage or assumptions change.
  Correspondence is not a claim that the two formalizations are equivalent.
- Preserve the independent Lean source policy: do not consult or copy the supplied
  external Lean artifact or ZIP. EasyCrypt may inform a coverage inventory, not
  serve as a proof-script translation source for new Lean development.
- Do not introduce admissions or weaken statements silently. Keep assumptions,
  algorithm refinements and trust boundaries explicit.
- Check Lean with (cd lean && lake build). Check EasyCrypt with its complete
  easycrypt/scripts/check-local.sh and the recorded prover toolchain. Both checks
  are required after layout changes; a proof edit requires its relevant check.
- Preserve historical release tags and source provenance. The paper is maintained
  in the separate miguel-ambrona/ffa-paper checkout and must remain unchanged
  unless explicitly requested. Current theoretical correspondence uses Lean only.
  Concrete arithmetic parameter validity and shifted EC identities are in scope;
  CI, whole-MSM wire layout and PLONK implementation remain outside scope.
