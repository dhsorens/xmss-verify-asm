#!/usr/bin/env bash
# The mutation boundary (PLAN M9), enforced rather than assumed.
#
# An untrusted optimizer proposes a patch. Lowering a number in the baseline
# file is the cheapest cheat available -- cheaper than weakening a proof -- so
# the boundary is a mechanical check on the candidate's diff, not a rule in a
# document. This script classifies every changed path into three buckets and
# fails on the first denied one.
#
#   scripts/check-mutation-boundary.sh [--base <ref>]
#
# Default base is HEAD, i.e. the candidate is the working tree. Untracked
# files count as changes.
#
# Exit 0 if nothing denied was touched, 1 otherwise, 2 on a usage error.
#
# THIS SCRIPT IS NOT CANDIDATE MATERIAL.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BASE="HEAD"
while [ $# -gt 0 ]; do
  case "$1" in
    --base) shift; BASE="${1:-}" ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) echo "check-mutation-boundary: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift
done

git rev-parse --verify "$BASE" >/dev/null 2>&1 \
  || { echo "check-mutation-boundary: no such ref '$BASE'" >&2; exit 2; }

# Tracked changes against the base, plus untracked files git does not ignore.
CHANGED="$( { git diff --name-only "$BASE"; git ls-files --others --exclude-standard; } \
  | sort -u )"

REGIONFILE="bench/regions.sha256"
[ -f "$REGIONFILE" ] || { echo "check-mutation-boundary: missing $REGIONFILE" >&2; exit 2; }

# The region pin. Always, even with an empty diff: an empty diff against the
# base says nothing about whether the pin itself is current.
check_regions() {
  local work; work="$(mktemp -d)"
  if ! lake build filter > "$work/build.log" 2>&1; then
    grep -E '^(error|warning):' "$work/build.log" | head -20 >&2
    printf '\ncheck-mutation-boundary: REJECT -- the candidate program does not elaborate,\n' >&2
    printf 'so the frozen regions cannot be listed.\n' >&2
    rm -rf "$work"; exit 1
  fi
  lake exe filter --regions > "$work/regions.txt" 2>/dev/null
  local want got
  want="$(grep -vE '^#' "$REGIONFILE" | tr -d '[:space:]')"
  got="$(shasum -a 256 < "$work/regions.txt" | cut -d' ' -f1)"
  if [ "$got" != "$want" ]; then
    printf 'expected %s\nactual   %s\n' "$want" "$got" >&2
    cp "$work/regions.txt" ./boundary-regions-actual.txt 2>/dev/null \
      && printf 'wrote the frozen-region listing to ./boundary-regions-actual.txt\n' >&2
    printf '\ncheck-mutation-boundary: REJECT -- a region outside the search space changed.\n' >&2
    printf 'Frozen: init, decode, chainsPre, chainLoad, chainStore, leaf, authPre,\n' >&2
    printf 'authSelect, authHash, final. The search space is chainStep and chainWalk\n' >&2
    printf '(plus the indices, lengths and offsets that are functions of the walk\n' >&2
    printf "length). Opening another region is a human decision, in its own commit.\n" >&2
    rm -rf "$work"; exit 1
  fi
  printf '  regions   %s frozen regions unchanged (%s)\n' \
    "$(grep -c '^## ' "$work/regions.txt")" "$got"
  rm -rf "$work"
}

if [ -z "$CHANGED" ]; then
  printf '== mutation boundary against %s ==\n' "$BASE"
  printf '  (no changed paths)\n'
  check_regions
  echo "check-mutation-boundary: OK -- no changes against $BASE, regions unchanged."
  exit 0
fi

# The search space: the designated region, the offsets and lengths that move
# with it, its local proof, and the symbolic-execution tactics (whose simp set
# names those offset lemmas). Nothing here can weaken a statement: the
# statements live on denied paths and are hashed by the statement pin.
is_allowed() {
  case "$1" in
    XmssAsm/Program/Verifier.lean) return 0 ;;
    XmssAsm/Regions/Chain.lean)    return 0 ;;
    XmssAsm/Regions/Common.lean)   return 0 ;;   # shared bridging lemmas
    XmssAsm/Machine/Sym.lean)      return 0 ;;
    README.md|PLAN.md|docs/*)      return 0 ;;   # documentation of a record
    bench/records/*)               return 0 ;;   # gate output, not candidate input
    *) return 1 ;;
  esac
}

# Frozen: theorem statements, the specification, the representation, the
# machine and oracle semantics, the benchmark definitions, the fixture corpus,
# the scoreboard, the gate, and the toolchain pins.
is_denied() {
  case "$1" in
    XmssAsm/Contract.lean)           return 0 ;;
    XmssAsm/Represent.lean)          return 0 ;;
    XmssAsm/Machine/Hash.lean)       return 0 ;;
    XmssAsm/Machine/Layout.lean)     return 0 ;;
    XmssAsm/Machine/Eval.lean)       return 0 ;;
    XmssAsm/Machine/Cost.lean)       return 0 ;;
    XmssAsm/Spec.lean|XmssAsm/Spec/*) return 0 ;;
    XmssAsm/Upstream.lean)           return 0 ;;
    XmssAsmTests/TestHash.lean)      return 0 ;;
    XmssAsmTests/Fixtures.lean)      return 0 ;;
    XmssAsmTests/Diff.lean)          return 0 ;;
    XmssAsmTests/Regions.lean)       return 0 ;;
    XmssAsmTests/Cost.lean)          return 0 ;;
    XmssAsmTests/Bench.lean)         return 0 ;;
    XmssAsmTests/Filter.lean)        return 0 ;;
    XmssAsmTests/Rejects.lean)       return 0 ;;
    XmssAsmTests/Main.lean)          return 0 ;;
    XmssAsmTests.lean)               return 0 ;;
    XmssAsmTools/*)                  return 0 ;;
    bench/*)                         return 0 ;;   # bench/records/* matched earlier
    scripts/*)                       return 0 ;;
    lakefile.toml|lake-manifest.json|lean-toolchain) return 0 ;;
    AGENTS.md|CLAUDE.md)             return 0 ;;
    AUTORESEARCH.md)                 return 0 ;;   # the loop's own instructions
    *) return 1 ;;
  esac
}

ALLOWED=""; DENIED=""; REPAIR=""
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if is_allowed "$f"; then ALLOWED="$ALLOWED $f"
  elif is_denied "$f"; then DENIED="$DENIED $f"
  else REPAIR="$REPAIR $f"
  fi
done <<< "$CHANGED"

printf '== mutation boundary against %s ==\n' "$BASE"
for f in $ALLOWED; do printf '  allowed   %s\n' "$f"; done
for f in $REPAIR;  do printf '  repair    %s\n' "$f"; done
for f in $DENIED;  do printf '  DENIED    %s\n' "$f"; done

if [ -n "$REPAIR" ]; then
  printf '\nnote: repair above the designated region. This is permitted -- the Lean\n'
  printf 'kernel is the trust boundary, not the file list -- but M8 makes region\n'
  printf 'insulation the iteration goal, so each of these is a robustness miss to\n'
  printf 'look at rather than a rule that was broken.\n'
fi

if [ -n "$DENIED" ]; then
  printf '\ncheck-mutation-boundary: REJECT -- the candidate touched frozen paths:\n' >&2
  for f in $DENIED; do printf '  %s\n' "$f" >&2; done
  printf '\nThese hold the theorem statements, the specification, the representation,\n' >&2
  printf 'the machine and oracle semantics, the benchmark definitions, the fixture\n' >&2
  printf 'corpus, the scoreboard, the gate, or the toolchain pins. A candidate may\n' >&2
  printf 'not edit them; only a human, in a separate commit, may.\n' >&2
  case " $DENIED " in
    *" bench/baseline.txt "*)
      printf '\nHint: bench/baseline.txt is also what `accept.sh --record` writes. If that\n' >&2
      printf 'is where this came from, commit the record and re-run; the gate is flagging\n' >&2
      printf 'its own uncommitted output, which is correct but not what you meant.\n' >&2 ;;
  esac
  exit 1
fi

# Only once the paths are clean: a denied path is the more important message.
check_regions

printf '\ncheck-mutation-boundary: OK -- nothing frozen was touched.\n'
exit 0
