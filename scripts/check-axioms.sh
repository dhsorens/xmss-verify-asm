#!/usr/bin/env bash
# Axiom gate: what the kernel actually recorded for this repository's own Lean.
#
# `XmssAsmTools/AxiomSweep.lean` walks every declaration under `XmssAsm` and
# `XmssAsmTools`, collects its axiom dependencies, and fails on anything outside
# the documented set (`propext`, `Classical.choice`, `Quot.sound`).
#
# Usage:
#   scripts/check-axioms.sh            # enforce; exit 1 on an undocumented axiom
#   scripts/check-axioms.sh --report   # print the census, exit 0
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# The sweep imports the built oleans, so the libraries have to exist; `lake env`
# is what puts them on LEAN_PATH.
lake build XmssAsm XmssAsmTools axiomsweep >/dev/null
exec lake env ./.lake/build/bin/axiomsweep "$@"
