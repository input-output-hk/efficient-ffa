# Independent Lean development

Use the paper as the mathematical specification and Lean/mathlib as the
proof foundation. The source policy and milestone status are in README.md.

- Do not inspect or copy the supplied sibling ForeignFieldArithPLONK-main
  repository or its ZIP archives when authoring this project. A later artifact
  comparison requires an explicit user request and a separately checked
  independent milestone.
- Use the EasyCrypt work as a coverage inventory, not as a proof-script
  translation source. Record any source consultation relevant to new proofs.
- Keep definitions concrete. Express algorithmic assumptions as theorem
  hypotheses or structures, not global project axioms.
- Do not use sorry, admit, new axioms, or native_decide to close proof goals.
  Prefer kernel-checked proofs and tactics. Keep theorem-axiom reports current.
- Do not weaken a paper statement silently. Record changed hypotheses,
  corrected algorithms and representation differences in the documentation.
- Build the library and regressions with lake build. Both are default targets
  and warnings are errors. Regenerate the manifest through Lake if dependency
  versions change; do not depend on absolute paths to another project.
- Preserve the sibling easycrypt/ formalization and separate paper repository.
  CI, larger instances and circuit implementation are outside the current scope.
