#!/usr/bin/env bash
# The accept gate (PLAN M8.a). One command: the only path by which a candidate
# program may land on `main`.
#
#   scripts/accept.sh                # judge the working tree; never writes
#   scripts/accept.sh --record       # ... and update the baseline on a record
#   scripts/accept.sh --metrics-out F  # also write the metric dump to F
#
# Exit codes:
#   0  gate pass  (m <= baseline; see below)
#   1  REJECT     (statement, proof, timeout, warning, gate script, test,
#                  hash pin, OTS constancy, or m > baseline)
#   2  usage / environment error
#
# A gate pass with `m == baseline` is allowed and is NOT a record: a refactor
# or a proof cleanup should be landable. Only `m < baseline` is a record, and
# only a record may be called an improvement or move the committed baseline.
#
# The score is the lexicographic pair `m = (OTS_STEPS, XMSS_EPMAX_STEPS)`.
# Hash counts are an exact pin, not a score term.
#
# THIS SCRIPT IS NOT CANDIDATE MATERIAL. Neither is `bench/baseline.txt`,
# `bench/statement.sha256`, the other `scripts/check-*.sh`, or the fixture
# corpus. A denylist that protects the theorem but not the scoreboard is the
# mismatch PLAN R8 warns about. Only a human, in a separate commit, changes
# the gate.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BASELINE="bench/baseline.txt"
PINFILE="bench/statement.sha256"
# Wall-clock budget for the proof check, in seconds. Proof-check time is
# excluded from the score but bounded as a gate condition: one candidate must
# not be able to stall the autoresearch loop (PLAN R10). A from-scratch check
# of this repository's own libraries takes ~30s, so this is ~20x headroom.
BUDGET="${ACCEPT_BUILD_BUDGET:-600}"

RECORD=0
METRICS_OUT=""
while [ $# -gt 0 ]; do
  case "$1" in
    --record) RECORD=1 ;;
    --metrics-out) shift; METRICS_OUT="${1:-}" ;;
    -h|--help) sed -n '2,30p' "$0"; exit 0 ;;
    *) echo "accept: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift
done

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

step()   { printf '\n== %s\n' "$*"; }
ok()     { printf 'ok    %s\n' "$*"; }
reject() { printf '\naccept: REJECT -- %s\n' "$*" >&2; exit 1; }

printf '== xmss-asm accept gate ==\n'
[ -f "$BASELINE" ] || { echo "accept: missing $BASELINE" >&2; exit 2; }
[ -f "$PINFILE" ]  || { echo "accept: missing $PINFILE" >&2; exit 2; }

# Read `KEY=VALUE` from a dump, ignoring comments.
get() { grep -E "^$1=" "$2" 2>/dev/null | head -1 | cut -d= -f2-; }

# `lake build <targets>` under the remaining wall-clock budget. Sets ELAPSED
# and BUILD_RC, accumulates PROOF_SECONDS, and rejects on timeout: exceeding
# the budget is a reject, not a slow pass, because one candidate must not be
# able to stall the autoresearch loop (PLAN R10).
PROOF_SECONDS=0
timed_build() {
  local targets="$1" log="$2" remaining start
  remaining=$(( BUDGET - PROOF_SECONDS ))
  [ "$remaining" -gt 0 ] || reject "proof check exceeded the ${BUDGET}s wall-clock budget"
  start=$(date +%s)
  # shellcheck disable=SC2086
  lake build $targets > "$log" 2>&1 &
  local pid=$! watchdog
  ( sleep "$remaining"; kill -TERM "$pid" 2>/dev/null; sleep 5
    kill -KILL "$pid" 2>/dev/null ) >/dev/null 2>&1 &
  watchdog=$!
  wait "$pid"; BUILD_RC=$?
  kill "$watchdog" 2>/dev/null; wait "$watchdog" 2>/dev/null
  ELAPSED=$(( $(date +%s) - start ))
  PROOF_SECONDS=$(( PROOF_SECONDS + ELAPSED ))
  if [ "$BUILD_RC" -ne 0 ] && [ "$PROOF_SECONDS" -ge "$BUDGET" ]; then
    reject "proof check exceeded the ${BUDGET}s wall-clock budget (killed at ${PROOF_SECONDS}s)"
  fi
}

# Reject if this build elaborated a module of ours that emitted a warning.
# Warnings are part of the work, not separate cleanup.
no_warnings() {
  if grep -qE '^warning: (XmssAsm|XmssAsmTests|XmssAsmTools)' "$1"; then
    grep -E '^warning: (XmssAsm|XmssAsmTests|XmssAsmTools)' "$1" | head -20 >&2
    reject "the build emitted warnings in this repository's own modules"
  fi
}

# ---------------------------------------------------------------------------
# 1. Statement integrity. First, because a weakened statement passes every
#    other check in this script and scores better.
# ---------------------------------------------------------------------------
step "1/7 statement integrity"
# The pin reads the built oleans, so the library has to be current: hashing a
# stale olean would let a weakened statement through, which is the one thing
# this step exists to catch. That build is part of the proof-check budget.
timed_build "XmssAsm XmssAsmTools statementpin" "$WORK/pinbuild.log"
if [ "$BUILD_RC" -ne 0 ]; then
  grep -E '^(error|warning):' "$WORK/pinbuild.log" | head -30 >&2
  reject "the library does not build, so the frozen statement cannot be checked"
fi
no_warnings "$WORK/pinbuild.log"
if ! lake env ./.lake/build/bin/statementpin > "$WORK/pin.txt" 2>"$WORK/pin.err"; then
  cat "$WORK/pin.err" >&2
  reject "a pinned constant is missing from the environment (see above)"
fi
EXPECTED="$(grep -vE '^#' "$PINFILE" | tr -d '[:space:]')"
ACTUAL="$(shasum -a 256 < "$WORK/pin.txt" | cut -d' ' -f1)"
if [ "$ACTUAL" != "$EXPECTED" ]; then
  printf 'expected %s\nactual   %s\n' "$EXPECTED" "$ACTUAL" >&2
  if cp "$WORK/pin.txt" ./accept-statement-actual.txt 2>/dev/null; then
    printf 'wrote the elaborated statement to ./accept-statement-actual.txt\n' >&2
    printf 'diff it against the pinned form before believing any re-pin\n' >&2
  fi
  reject "the frozen statement changed (VerifierCorrect / Represents / layout / oracle)"
fi
ok "$(grep -c ' : ' "$WORK/pin.txt") pinned forms hash to $ACTUAL"

# ---------------------------------------------------------------------------
# 2. The rest of the proof check (tests and tooling), same budget.
# ---------------------------------------------------------------------------
step "2/7 lake build (budget ${BUDGET}s total)"
timed_build "" "$WORK/build.log"
if [ "$BUILD_RC" -ne 0 ]; then
  grep -E '^(error|warning):' "$WORK/build.log" | head -30 >&2
  reject "lake build failed (${PROOF_SECONDS}s); xmss_verify_correct does not typecheck"
fi
no_warnings "$WORK/build.log"
ok "proofs check in ${PROOF_SECONDS}s, no warnings in re-elaborated modules"

# ---------------------------------------------------------------------------
# 3. Trust gates: kernel-recorded axioms, and the forbidden-tactic scan.
# ---------------------------------------------------------------------------
step "3/7 trust gates"
scripts/check-axioms.sh > "$WORK/axioms.log" 2>&1 \
  || { tail -20 "$WORK/axioms.log" >&2; reject "the axiom gate failed"; }
ok "$(tail -1 "$WORK/axioms.log")"
scripts/check-forbidden-tactics.sh > "$WORK/tactics.log" 2>&1 \
  || { tail -20 "$WORK/tactics.log" >&2; reject "the forbidden-tactic gate failed"; }
ok "$(tail -1 "$WORK/tactics.log")"

# ---------------------------------------------------------------------------
# 4. Differential suite on the one program.
# ---------------------------------------------------------------------------
step "4/7 differential suite"
if ! scripts/test-differential.sh > "$WORK/diff.log" 2>&1; then
  grep -E '^FAIL' "$WORK/diff.log" | head -20 >&2
  tail -3 "$WORK/diff.log" >&2
  reject "the differential suite failed"
fi
ok "$(grep -E 'failures$' "$WORK/diff.log" | tail -1)"

# ---------------------------------------------------------------------------
# 5. Hash pin (exact) and OTS constancy.
# ---------------------------------------------------------------------------
step "5/7 hash pin and OTS constancy"
if ! lake exe bench > "$WORK/metrics.txt" 2>"$WORK/bench.err"; then
  cat "$WORK/bench.err" >&2
  reject "the metric dump failed to measure the program"
fi
[ -n "$METRICS_OUT" ] && { cp "$WORK/metrics.txt" "$METRICS_OUT"
  printf "PROOF_CHECK_SECONDS=%s\n" "$PROOF_SECONDS" >> "$METRICS_OUT"; }

for k in OTS_HASHES XMSS_EPMAX_HASHES; do
  want="$(get "$k" "$BASELINE")"; got="$(get "$k" "$WORK/metrics.txt")"
  [ -n "$got" ] || reject "the metric dump has no $k"
  [ "$got" = "$want" ] || reject "hash pin: $k is $got, the pin is $want \
(fewer oracle queries means a different computation, not a faster one)"
done
ok "hash pin exact: OTS $(get OTS_HASHES "$WORK/metrics.txt"), \
XMSS $(get XMSS_EPMAX_HASHES "$WORK/metrics.txt")"
DISTINCT="$(get OTS_STEPS_DISTINCT "$WORK/metrics.txt")"
[ "$DISTINCT" = "1" ] || reject "OTS constancy: OTS_STEPS takes $DISTINCT distinct values \
across accepting fixtures, so 'OTS steps on an accepting path' is not well defined"
ok "OTS step count is the same on all $(get ACCEPTING_FIXTURES "$WORK/metrics.txt") \
accepting fixtures"
for k in ACCEPTING_FIXTURES CORPUS_FIXTURES; do
  want="$(get "$k" "$BASELINE")"; got="$(get "$k" "$WORK/metrics.txt")"
  [ "$got" = "$want" ] || reject "the fixture corpus changed: $k is $got, baseline $want \
(the corpus is not candidate material)"
done
ok "fixture corpus unchanged"

# ---------------------------------------------------------------------------
# 6. The metric dump against the committed baseline.
# ---------------------------------------------------------------------------
step "6/7 score against the baseline"
B_OTS="$(get OTS_STEPS "$BASELINE")";        C_OTS="$(get OTS_STEPS "$WORK/metrics.txt")"
B_XMSS="$(get XMSS_EPMAX_STEPS "$BASELINE")"; C_XMSS="$(get XMSS_EPMAX_STEPS "$WORK/metrics.txt")"
for v in "$B_OTS" "$C_OTS" "$B_XMSS" "$C_XMSS"; do
  case "$v" in ''|*[!0-9]*) reject "unparseable score component '$v'" ;; esac
done
printf '      %-22s %10s %10s\n' metric baseline candidate
printf '      %-22s %10s %10s\n' OTS_STEPS "$B_OTS" "$C_OTS"
printf '      %-22s %10s %10s\n' XMSS_EPMAX_STEPS "$B_XMSS" "$C_XMSS"
printf '      %-22s %10s %10s\n' STATIC_INSTRUCTIONS \
  "$(get STATIC_INSTRUCTIONS "$BASELINE")" "$(get STATIC_INSTRUCTIONS "$WORK/metrics.txt")"
printf '      %-22s %10s %10s\n' AUTH_EPMAX_STEPS \
  "$(get AUTH_EPMAX_STEPS "$BASELINE")" "$(get AUTH_EPMAX_STEPS "$WORK/metrics.txt")"
printf '      %-22s %10s %10s\n' PROOF_CHECK_SECONDS "(not scored)" "$PROOF_SECONDS"

# Lexicographic comparison of m = (OTS_STEPS, XMSS_EPMAX_STEPS).
if   [ "$C_OTS" -lt "$B_OTS" ]; then CMP=-1
elif [ "$C_OTS" -gt "$B_OTS" ]; then CMP=1
elif [ "$C_XMSS" -lt "$B_XMSS" ]; then CMP=-1
elif [ "$C_XMSS" -gt "$B_XMSS" ]; then CMP=1
else CMP=0; fi

step "7/7 verdict"
if [ "$CMP" -gt 0 ]; then
  reject "m > baseline: ($C_OTS, $C_XMSS) is worse than ($B_OTS, $B_XMSS). \
The theorem holding is not enough."
fi
if [ "$CMP" -eq 0 ]; then
  ok "GATE PASS, not a record: m == baseline ($B_OTS, $B_XMSS). Baseline unchanged."
  printf '\naccept: PASS\n'
  exit 0
fi

ok "NEW RECORD: ($C_OTS, $C_XMSS) < ($B_OTS, $B_XMSS)"
if [ "$RECORD" -eq 1 ]; then
  # Rewrite only the values, keeping the file's documentation.
  TMP="$WORK/baseline.new"
  cp "$BASELINE" "$TMP"
  while IFS='=' read -r k v; do
    case "$k" in ''|'#'*) continue ;; esac
    if grep -qE "^$k=" "$TMP"; then
      awk -v k="$k" -v v="$v" -F= '$1==k { print k "=" v; next } { print }' "$TMP" > "$TMP.2"
      mv "$TMP.2" "$TMP"
    else
      printf '%s=%s\n' "$k" "$v" >> "$TMP"
    fi
  done < "$WORK/metrics.txt"
  mv "$TMP" "$BASELINE"
  ok "baseline updated (commit it with the candidate; git is the leaderboard)"
else
  ok "baseline NOT updated; re-run with --record to move the scoreboard"
fi
printf '\naccept: PASS (new record)\n'
exit 0
