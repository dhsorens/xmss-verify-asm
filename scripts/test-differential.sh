#!/usr/bin/env bash
# End-to-end differential test and cycle report.
#
# Runs the RV64 verifier under `stepH H_test` on every fixture of the corpus
# and compares `a0` with `Concrete.verify` evaluated under `H_test`
# (`XmssAsm.specVerify`, equal to the spec by `specVerify_eq`). Also runs the
# component-level region suites when present in the executable.
#
# Usage:
#   scripts/test-differential.sh            # hash cost 1
#   scripts/test-differential.sh 100        # hash cost 100 for the cycle report
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
lake build difftest >/dev/null
exec lake exe difftest "$@"
