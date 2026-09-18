# Running the autoresearch loop

*This file is not candidate material: an agent running the loop may not edit
it, and the mutation boundary enforces that.*

This repository is set up so that an untrusted agent can propose changes to the
verifier's hot loop and get a yes/no plus numbers, without anyone having to
trust the agent. The trust boundary is the Lean kernel, not the agent's
reasoning and not its test results.

The prompt is in [The prompt](#the-prompt) below. Everything before it is
context for the human deciding whether to run the loop; everything after it is
context the agent will want once it is running.

## What the loop is, in one paragraph

`main` holds one RV64IM implementation of the XMSS verifier and one theorem
that it is correct. A candidate is a patch to the chain walk. One command,
`scripts/autoresearch.sh`, checks that the patch stayed inside its search
space, cheaply rejects it if the interpreter disagrees with the specification,
then pays for a full proof check and scores it against a committed baseline. A
candidate that is faster and still proved becomes the new record and overwrites
`main`. Git history is the leaderboard; losing candidates are not kept as
programs.

## Before you start

```bash
lake exe cache get      # Mathlib oleans; without this the first build is an hour
lake build              # ~33s from scratch for this repo's own libraries
scripts/accept.sh --no-boundary
```

The last command should print `accept: PASS` and `m == baseline`. If it does
not, fix that first: the loop cannot tell a candidate's failure from a broken
starting tree.

Two costs worth knowing before you point an agent at this. On a warm tree the
cheap filter is about ten seconds and a full candidate judgement well under a
minute, of which the proof check itself is a handful, so the loop is cheap to
iterate. But
the proof repair is where an agent will spend its time, and it is real Lean
work on symbolic-execution proofs; budget accordingly.

## The prompt

Give an agent the repository and the following. It is written to be pasted as
is.

> You are optimizing the chain walk of a formally verified XMSS verifier
> written in RISC-V (RV64IM) assembly inside Lean 4. Your goal is to make it
> execute fewer instructions while keeping it proved correct.
>
> **The score.** `m = (OTS_steps, XMSS_epmax_steps)`, compared
> lexicographically against the committed baseline in `bench/baseline.txt`.
> Lower is better. `m < baseline` is a new record; `m == baseline` passes but
> is not a record; `m > baseline` fails even if every proof still closes.
> Hash-call counts are an exact pin, not a score term: a candidate that
> queries the hash oracle a different number of times is computing something
> else and fails.
>
> **The one command.**
>
> ```bash
> scripts/autoresearch.sh            # judge the working tree, write nothing
> scripts/autoresearch.sh --record   # land a new record
> ```
>
> It runs three tiers in order: the mutation boundary, the cheap
> interpreter-only filter (`lake exe filter`, about ten seconds, builds none of
> the region proofs), and the accept gate (`scripts/accept.sh`, the statement pin, the
> proof check under a wall-clock budget, both trust gates, the differential
> suite, the hash pin and the score). Exit 0 means gate pass. Read its output;
> it says which tier rejected you and why.
>
> **What you may change.** `chainStep` and `chainWalk` in
> `XmssAsm/Program/Verifier.lean`, the lemmas that state their length and
> branch offsets (`chainWalk_length`, `bOff_chainWalk`, `bOff_chainBack`,
> `bOff_chainsLoop`), the offset-lemma names in the simp set in
> `XmssAsm/Machine/Sym.lean`, and the local proof in
> `XmssAsm/Regions/Chain.lean` (plus shared bridging lemmas in
> `XmssAsm/Regions/Common.lean` if you need one). Region *indices* are already
> stated relative to `chainWalk.length`, so they move on their own; do not
> hard-code them.
>
> **What you may not change, ever.** The theorem statements
> (`VerifierCorrect`, `xmss_verify_correct`), the specification, the memory
> representation, the machine and hash-oracle semantics, the benchmark
> definitions, the fixture corpus, `bench/*`, `scripts/*`, and every region
> other than `chainStep` / `chainWalk` (`init`, `decode`, `chainsPre`,
> `chainLoad`, `chainStore`, `leaf`, `authPre`, `authSelect`, `authHash`,
> `final`). All of this is enforced mechanically and checked before anything
> expensive runs, so there is no point attempting it: the boundary check reads
> your diff, and separate hashes pin the elaborated statements and the frozen
> regions' instruction lists. If you think a frozen thing has to change, stop
> and say so in plain words instead of changing it.
>
> **Proof repair is expected, not a workaround.** You will break
> `XmssAsm/Regions/Chain.lean` and you are supposed to fix it. What makes a
> repair valid is that it re-establishes the *same* local contracts
> (`ChainWalkPre`, `ChainWalkPost`, including the write set `WChain`) and the
> *unchanged* top-level `xmss_verify_correct`. Never use `sorry`. Never use
> `native_decide` or `bv_decide`; a gate script scans for them. Never weaken a
> contract to make a proof close. If you widen `WChain`, say so explicitly in
> your report, because it is a weaker guarantee to every caller.
>
> **A green test suite is not a merge gate.** If the interpreter agrees with
> the specification on all 104 fixtures but `chainWalk_correct` does not close,
> the candidate is rejected. Do not argue from test results.
>
> **Work in this order.**
> 1. Read `docs/CONTRACT.md`, section "The optimization contract", and the
>    reject archive `XmssAsmTests/Rejects.lean` so you do not rediscover a
>    known dead end.
> 2. Change `chainStep` / `chainWalk` and run `lake exe filter`. It imports no
>    region proof, so it is fast and it still works while `Chain.lean` is
>    broken. If the
>    filter rejects, you computed the wrong thing; fix that before proving
>    anything.
> 3. Repair `XmssAsm/Regions/Chain.lean` until `lake build` is clean, with no
>    new warnings. Warnings are part of the work.
> 4. Run `scripts/autoresearch.sh`. If it passes and reports a new record, run
>    it again with `--record` and commit `bench/baseline.txt` and the new file
>    under `bench/records/` together with your change.
> 5. Report truthfully: the numbers, what you changed, which files you had to
>    repair, and anything you assumed. If you had to edit a proof *above*
>    `chainWalk_correct`, say so; it is allowed but it means the region
>    insulation did not hold, which is worth knowing.
>
> **When a candidate fails for an interesting reason,** add it to
> `XmssAsmTests/Rejects.lean` as an instruction list plus the failure it
> produces, so the next attempt does not repeat it. That file is test data;
> nothing outside it may refer to those lists.
>
> **Stop and ask a human** if you cannot close a proof after a genuine effort,
> if the only way forward is through something frozen, or if you find what
> looks like a hole in the gate. A reported hole is worth more than a record.

## Where the instructions actually go

The numbers an agent needs to aim. The one-time-signature path is 2139 steps:

| part | steps |
|---|---|
| init (encoding hash) | 43 |
| decode digits | 222 |
| 42 chain walks | 1858 |
| leaf hash | 16 |

and the 1858 is

| part | steps |
|---|---|
| chain-loop overhead, 42 x 20 (load 9, store 10, branch 1) | 840 |
| walk prologue, 42 x 10 | 420 |
| per-step work, 99 x 5 | 495 |
| hash `ECALL`s | 99 |
| loop header | 4 |

Only the last three rows are inside the search space. The walk is
`10 + 6 (7 - x)` steps for digit `x`: ten to hoist the constants and guard the
loop once, then five instructions and one branch per step. `chainStep` is
five instructions:

```
SLLI x6, x15, 32      # tweak word from the chain position in x15
ADDI x6, x6, 0x100    # the chain-tweak tag
SD   x7, x6, 0        # store the tweak at BUFA
ECALL                 # hash BUFA..+48 -> CUR, in place
ADDI x15, x15, 1      # advance the position
```

The `ECALL` and the tweak store are close to forced: the hash count is pinned,
and the tweak word differs every step because the position does. So the room
inside the search space is roughly the other three instructions per step, the
ten-instruction prologue and the branch. That is a few hundred steps, not a
few thousand.

`bench/baseline.txt` records `TARGET_OTS_STEPS=512` as what "really good"
would look like. Reaching it needs `decode` and the chain load/store overhead,
which are outside this search space; opening a region is a human decision. See
"What really good would look like" in `docs/CONTRACT.md` for the arithmetic.

## Proof-repair notes

The chain-walk proof is symbolic execution over a machine state kept as a flat
record literal. `XmssAsm/Machine/Sym.lean` has the tactics and the header
comment explaining them. Three things that cost real time here, so that they
cost less next time:

- **`sym_code hC [chainWalk] [chainStep]`** unfolds the `CodeAt` hypothesis
  into one fetch fact per instruction, which you then destructure positionally
  (`obtain ⟨f0, f1, ...⟩`). Change the instruction count and every index
  shifts; the fetch fact `fN` is always instruction `N` of the region.
- **Resolve an `if` before `sym_norm` sees it.** `ChainInv` states the loop
  position as `if k < 7 - x.val then <body> else <after the region>`. Putting
  that in front of `sym_norm` is a heartbeat timeout, because the simp set
  tries to decide `0 < 7 - x.val` for a `Fin` projection. `rw [if_pos ...]`
  first, then normalise. The same shape with a plain variable bound, as in
  `AuthInv`'s `if L < 32`, does not trip it, which is what makes it confusing.
- **Do not rewrite values into the state before a hash call.** Rewriting tweak
  values into the symbolic state ahead of an `ECALL` took one authentication
  proof from nine seconds to a kernel timeout. Defer every value rewrite to
  the hash-input side goal.

For the branch conditions, `slt_ofNat` turns a signed compare of small
naturals into a decidable `Nat` comparison; state the branch fact as
`... = true` or `... = false` for the case you are in and resolve the `if`
with `if_pos` / `if_neg` rather than letting `simp` search.

## What the harness guarantees, and what it does not

It guarantees that anything landing on `main` re-establishes the unchanged
`xmss_verify_correct` for the exact program the evaluator measured, resting
only on `propext`, `Classical.choice` and `Quot.sound`; that the statements,
representation, oracle semantics, benchmark and frozen regions are
byte-identical in meaning to their pinned form; and that the baseline moves
only on a strict improvement.

It does not guarantee that the program is optimal. There is no lower-bound
theorem here, and the loop is best-so-far. It also does not model a real
prover: the cost model is one virtual cycle per executed instruction, with the
hash a single abstract `ECALL`. A candidate that wins here wins on RV
instruction overhead, which is the thing this project set out to measure.
