#!/usr/bin/env bash
# The autoresearch harness (PLAN M9): one command that evaluates a candidate
# patch to the chain walk end to end and answers yes/no plus numbers.
#
#   scripts/autoresearch.sh                 # judge the working tree, write nothing
#   scripts/autoresearch.sh --record        # ... and land a new record
#   scripts/autoresearch.sh --base <ref>    # judge the diff against <ref>
#   scripts/autoresearch.sh --skip-filter   # go straight to the accept gate
#
# Exit codes:
#   0  gate pass  (0 with "new record" on the last line if it is one)
#   1  reject, at whichever stage said so
#   2  usage / environment error
#
# Two tiers, and the split is the point.
#
#   1. mutation boundary  -- what the candidate is allowed to have touched.
#      Mechanical, on the diff. Lowering a number in the baseline file is
#      cheaper than weakening a proof, so this is checked first and is not a
#      rule in a document.
#
#   2. inner filter       -- `lake exe filter`, the interpreter only. It
#      imports no region proof, so it builds and runs while the candidate's
#      proof is still broken, and rejects a wrong chain walk in seconds. It
#      is NOT a merge gate; a green filter on a candidate whose
#      `chainWalk_correct` does not close is a reject.
#
#   3. accept gate        -- `scripts/accept.sh`. The statement pin, the proof
#      check under a wall-clock budget, both trust gates, the differential
#      suite with the reject archive, the exact hash pin, OTS constancy, and
#      the score against the committed baseline. The Lean kernel is the trust
#      boundary. Differential tests are never a substitute for the theorem.
#
# The optimizer is not trusted. Correctness is the same theorem and the same
# gates as manual work.
#
# THIS SCRIPT IS NOT CANDIDATE MATERIAL.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

RECORD=0
BASE="HEAD"
SKIP_FILTER=0
while [ $# -gt 0 ]; do
  case "$1" in
    --record) RECORD=1 ;;
    --base) shift; BASE="${1:-}" ;;
    --skip-filter) SKIP_FILTER=1 ;;
    -h|--help) sed -n '2,37p' "$0"; exit 0 ;;
    *) echo "autoresearch: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift
done

banner() { printf '\n########## %s\n' "$*"; }
die()    { printf '\nautoresearch: REJECT at %s\n' "$*" >&2; exit 1; }

printf '== xmss-asm autoresearch: judging the working tree against %s ==\n' "$BASE"

banner "tier 1: the mutation boundary"
scripts/check-mutation-boundary.sh --base "$BASE" || die "the mutation boundary"

if [ "$SKIP_FILTER" -eq 0 ]; then
  banner "tier 2: the inner filter (no proof is checked)"
  if ! lake build filter > /tmp/autoresearch-filter-build.log 2>&1; then
    grep -E '^(error|warning):' /tmp/autoresearch-filter-build.log | head -20 >&2
    die "the inner filter's own build -- the candidate program does not elaborate"
  fi
  lake exe filter || die "the inner filter (interpreter disagrees with the specification, \
or the hash pin moved)"
else
  banner "tier 2: the inner filter -- SKIPPED by --skip-filter"
fi

banner "tier 3: the accept gate"
if [ "$RECORD" -eq 1 ]; then
  scripts/accept.sh --base "$BASE" --record; GRC=$?
else
  scripts/accept.sh --base "$BASE"; GRC=$?
fi
[ "$GRC" -eq 0 ] || die "the accept gate"

printf '\nautoresearch: PASS\n'
if [ "$RECORD" -eq 1 ]; then
  printf 'If the gate reported a new record, bench/baseline.txt and bench/records/\n'
  printf 'have been updated; commit them with the candidate. Git is the leaderboard.\n'
else
  printf 'Nothing was written. Re-run with --record to land a new record.\n'
fi
exit 0
