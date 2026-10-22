#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/package-msm.py --check
python3 scripts/check-proof-policy.py
checker="${EASYCRYPT:-easycrypt}"
options=(compile -no-eco -I . -I tests -p Alt-Ergo -p Z3 -timeout 5 -pragmas Proofs:check)
log="$(mktemp)"
trap 'rm -f "$log"' EXIT

# Check each local theory independently: ordinary imports do not check proofs.
shopt -s nullglob
for theory in *.ec *.eca tests/*.ec; do
  case "$theory" in tests/*MustFail.ec) continue ;; esac
  printf 'Checking %s\n' "$theory"
  if ! "$checker" "${options[@]}" "$@" "$theory" >"$log" 2>&1; then
    cat "$log" >&2
    exit 1
  fi
done

for negative in tests/*MustFail.ec; do
  printf 'Checking expected rejection of %s\n' "$negative"
  if "$checker" "${options[@]}" "$@" "$negative" >"$log" 2>&1; then
    echo "ERROR: an invalid theorem was proved: $negative" >&2
    exit 1
  fi
  if ! grep -q 'cannot prove goal (strict)' "$log"; then
    cat "$log" >&2
    echo "ERROR: the negative test failed for an unexpected reason." >&2
    exit 1
  fi
done
echo "All local proofs checked; all negative regressions rejected."
