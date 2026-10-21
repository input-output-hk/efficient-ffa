#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

checker="${EASYCRYPT:-easycrypt}"
options=(compile -no-eco -I . -p Alt-Ergo -p Z3 -timeout 5)
# Extra arguments, e.g. -why3 /path/to/why3.conf, are forwarded to EasyCrypt.
for theory in \
  MultiScalarMul_Abstract_Setup.ec \
  AuxResults.ec \
  IterationProps.ec \
  MultiScalarMul_Abstract.ec \
  MultiScalarMul_Abstract_Soundness.ec \
  MultiScalarMul_Abstract_Completeness.ec \
  tests/MSM_Regression.ec
do
  printf 'Checking %s\n' "$theory"
  "$checker" "${options[@]}" "$@" "$theory"
done

log="$(mktemp)"
trap 'rm -f "$log"' EXIT
for negative in tests/LegacyAxiomMustFail.ec tests/NegativeIterationsMustFail.ec
do
  printf 'Checking expected rejection of %s\n' "$negative"
  if "$checker" "${options[@]}" "$@" "$negative" >"$log" 2>&1; then
    echo "ERROR: a legacy contradiction was proved: $negative" >&2
    exit 1
  fi
  if ! grep -q 'cannot prove goal (strict)' "$log"; then
    cat "$log" >&2
    echo "ERROR: the negative test failed for an unexpected reason." >&2
    exit 1
  fi
done
echo "All local MSM proofs checked; both legacy contradictions rejected."
