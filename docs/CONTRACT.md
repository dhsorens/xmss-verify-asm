# The machine/specification contract

What the RV64 verifier promises, stated once (M1) and discharged in M7. Lean
is authoritative; this file is the guided tour and the adversarial review.

| piece | where |
|---|---|
| hash-call boundary `HashContract H` | `XmssAsm/Machine/Hash.lean` (`stepH`, `hashEffect`, `hashArgsValid`) |
| memory layout and encodings | `XmssAsm/Machine/Layout.lean` |
| representation relation | `XmssAsm/Represent.lean` (`Represents`, `initState`) |
| the program | `XmssAsm/Program/Verifier.lean` (`verifier`, `verifierCode`) |
| the theorem statement | `XmssAsm/Contract.lean` (`VerifierCorrect`) |
| the evaluator and cost model | `XmssAsm/Machine/Eval.lean` (`runH`, `Stats.cost`) |
| the spec, evaluated | `XmssAsm/Spec/Eval.lean` (`evalH`, `evalH_verify`, `specVerify`) |

## Entry convention

The machine starts with `pc = CODE_BASE = 0x1000` and `code = verifierCode`,
i.e. the code map is exactly `loadProgram CODE_BASE verifier`. Registers,
scratch memory and the host-I/O fields (`committed`, `publicValues`,
`privateInput`, `inputBufBase`) are arbitrary. The program ends at a `HALT`
syscall (`ECALL` with `x5 = 0`) with the Boolean result in `x10`: `1` for
accept, `0` for reject.

## The abstract hash oracle

`H : List UInt8 → BitVec 256` is a parameter of everything. The code reaches
it through one `ECALL` shape, interpreted by `stepH H`:

```
x5  = HASH_ID (0x48415348)
x10 = byte address of the input      x11 = input length in bytes
x12 = byte address of the output, 8-aligned
```

Effect: the 32 bytes `H(mem[x10 .. x10+x11))` are written at `x12` as four
little-endian doublewords; `pc += 4`; nothing else changes. The call traps if
the input range or any output doubleword is outside valid machine memory
(`hashArgsValid`). Every other instruction is `RiscvZkvm.Rv64.step`
unchanged (`stepH_of_step`), so the only semantics added to the RV64 model is
this one contract. No backend, no BLAKE2s, no host ABI.

The input bytes are read with the model's own `readBytes`, so the identity
"48 doublewords in memory = these bytes" is a theorem about the model
(`XmssAsm.Spec.Bytes`), not an assumption.

### Overlapping input and output

`hashEffect` reads the input from the pre-state and writes the output to the
post-state, so `[x12, x12 + 32)` may overlap `[x10, x10 + x11)`. The chain
walk relies on that: it sets `x12 = CUR = BUFA + 32`, the payload slot of its
own hash input, so the oracle writes the next chain value straight into the
slot the next step will hash, and the walk never copies the digest at all.
That is four instructions per chain step, 396 over an accepting run.

This is a property of the model, not a convention it inherited, so it is worth
saying why it also holds of any implementation. A hash output depends on every
input byte, so no correct implementation can emit an output byte before it has
absorbed the whole input; read-then-write is forced. What remains is a *host*
assumption: that the prover's hash syscall does not itself reject or mishandle
an output buffer overlapping its input buffer. If a target host does, the fix
is to tighten `hashArgsValid` to require disjointness -- which is a change to
the frozen oracle semantics, hence a human decision, and it would retroactively
reject this chain walk.

## Layout

All input and scratch cells are doubleword-aligned literals in the legacy
zone `[0x20, 0x78000000]`; validity of every access is `decide`.

```
inputs (read only)                     scratch (the only memory written)
ROOT   0x10000  pk.root      16 B      BUFA   0x10500  tweak ‖ P ‖ payload(≤64)
PARAM  0x10010  pk.parameter 16 B      CUR    0x10520  = BUFA payload: current value
EPOCH  0x10020  ep           8 B       OUT    0x10560  hash output 32 B
MSG    0x10028  message      32 B      DIGITS 0x10580  42 doublewords
RHO    0x10048  sig.randomness 24 B    BUFL   0x10740  tweak ‖ P ‖ 42 endpoints
CHAINS 0x10060  sig.chainValue i at +16 i     ENDPTS 0x10760  endpoint i at +16 i
AUTH   0x10300  sig.authPath l at +16 l       SCRATCH = [0x10500, 0x10A20)
```

A digest `d : BitVec 128` is two doublewords `d[0:64)`, `d[64:128)`. An epoch
is one doubleword holding `ep.val` (`< 2^32`). A tweak is two doublewords
`tag·2^8 + position·2^32` and `epoch·2^32` (`tweakBytes` unfolds to exactly
these 16 little-endian bytes: `XmssAsm.Spec.Bytes`).

## The theorem (`VerifierCorrect H`)

For all `pk ep msg sig` and all `s` with `s.code = verifierCode`,
`s.pc = CODE_BASE`, `Represents s pk ep msg sig`, there is `s'` with

* `Reaches H s s'` -- finitely many `stepH H` steps (termination);
* `Decomp.SyscallHalted s'` and `stepH H s' = none` -- halted, by the halt
  syscall, and the machine really stops;
* `s'.getReg x10 = resultWord (evalH H (Concrete.verify pk ep msg sig))` --
  the Boolean of the upstream verifier, evaluated with every oracle query
  answered by `H` (VCVio's `evalWithAnswerFn`, the spec's own idiom);
* `Frame InScratch s s'` -- code and host-I/O fields unchanged, memory outside
  `[0x10500, 0x10A20)` unchanged, registers outside `CLOB` unchanged.

`Concrete.verify` is the spec's definition, imported verbatim; the result is
related to it directly, parametrically in `H`. There is no second verifier.

## Cost model

```
ordinary executed RV instruction = 1 virtual cycle
abstract hash call (HASH_ID ECALL) = hashCost virtual cycles   (default 1)
```

Branches, loads and stores are ordinary instructions. The halting `ECALL` is
not executed (the machine stops at it) and is not counted. The evaluator
(`runH`) runs `stepH H` on `verifier` -- the same function and the same value
the theorem is about -- and reports `steps`, `hashes`, `ordinary = steps -
hashes` and `cost = ordinary + hashes·hashCost`. Execution is input dependent
(reject paths are short; the authentication step's cost depends on the epoch
bits), so a reported number always names its fixture; the benchmark path is
"valid verification", whose hash count is the constant 133 = 1 + 99 + 1 + 32.

## Region contracts (M2/M3)

Every region theorem has the shape

```
CodeAt s.code (addr idxRegion) region 0 → Pre s → Runs H s Post
```

`Runs H s Q := ∃ s', Reaches H s s' ∧ Q s'` is total correctness under the
hash-oracle stepper: termination is part of the claim. `CodeAt C base prog 0`
says only that `prog` sits at `base`; it is discharged for the artifact by
`decide +kernel` (`verifierCode_chainWalk`), so a region theorem never
depends on the rest of the program, and callers compose regions with
`Runs.bind`/`Runs.loop`.

The six regions and their contracts:

| region | file | contract |
|---|---|---|
| init | `Regions/Init.lean` | `P` in both hash buffers, the encoding digest in `x20`/`x21` |
| decode | `Regions/Decode.lean` | `TargetSum.decodeDigest`: digits in `DIGITS`, or halt with `a0 = 0` |
| chains | `Regions/Chains.lean` | every `ENDPTS` slot holds `recoverChain` of its chain |
| leaf | `Regions/Leaf.lean` | `CUR` holds `leafHash` of the endpoints |
| auth | `Regions/Auth.lean` | `CUR` holds `authenticationRoot` after 32 levels |
| final | `Regions/Final.lean` | halt with `a0 = 1` exactly when `CUR = ROOT` |

`XmssAsm/Verify.lean` composes them with `Runs.bind`; a region is connected to
the next only through its postcondition and its frame, so the memory facts a
later region needs are transported by `Frame.mem` rather than re-derived.

The chain walk (`XmssAsm/Regions/Chain.lean`) is the template:

* `ChainWalkPre s P ep i x v`: `pc = addr idxChainWalk`, `x8 = ep`,
  `x14 = x`, `x16 = 8 i`, `BUFA_P = P`, `CUR = v`.
* `ChainWalkPost H s P ep i x v pcEnd s'`: `pc = pcEnd`, `x8 x13 x16 x18 x19`
  unchanged, `BUFA_P = P`, `CUR = recoverChain P ep i x v` evaluated under `H`,
  and `Frame WChain s s'` (`WChain` = the tweak doublewords of `BUFA` and the
  32 bytes at `CUR`; every other memory cell and every register outside `CLOB`
  unchanged). `CUR` for 32 rather than 16 bytes because the oracle's output
  block lands there: the digest in the payload slot, its unused upper half in
  `CUR2`. The walk does not touch `OUT` at all. Both are scratch, so
  `Frame InScratch` at the top is unaffected, but a caller may not assume
  `CUR2` survives a chain walk.

The executable frame check in `XmssAsmTests.Regions` is `decide` of these very
predicates, not a hand-written copy: a copy drifts the first time a candidate
changes a write set, and it drifts silently.

One lesson from repairing this proof, since it cost an hour and will recur.
The walk's loop is rotated, so `ChainInv` states its pc as
`if k < 7 - x.val then <body> else <after the region>`. Putting that `if` in
front of `sym_norm` costs a heartbeat timeout: the simp set tries to decide
`0 < 7 - x.val` for a `Fin` projection. Resolve the `if` first
(`rw [if_pos ...]`) and then normalise. The same shape with a plain variable
bound, as in `AuthInv`'s `if L < 32`, does not trip it, which is what made it
confusing.

**One implementation satisfies it: `chainWalk_correct`.** The contract is
reached through four declared swap sites -- `chainWalk` (the program),
`chainWalk_length`, `bOff_chainsLoop` (the loop branch offset that depends on
it) and `chainWalk_correct` (the theorem callers use) -- and that is the
interface a candidate patches.

During M3 the same contract was satisfied by two sequences, a straightforward
walk and a hoisted one, swapped in both directions on 2026-09-17 with no other
change. That was a proof-architecture checkpoint, not a shipping arrangement:
it showed the boundary is real. M8.a collapsed it, because a live alternate
`Program` a caller could select is exactly what makes "the program the theorem
is about" ambiguous. Git history keeps the experiment; `main` does not.

### Cycle counts of the chain walk

`difftest` runs the walk from a fresh entry state (starting digest 0, epoch 0,
chain 0) for every digit; `steps` counts executed instructions including the
hash calls, `hashes` the hash calls among them.

| digit `x` | hashes `7 - x` | steps |
|---|---|---|
| 0 | 7 | 52 |
| 1 | 6 | 46 |
| 2 | 5 | 40 |
| 3 | 4 | 34 |
| 4 | 3 | 28 |
| 5 | 2 | 22 |
| 6 | 1 | 16 |
| 7 | 0 | 10 |

That is `10 + 6 (7 - x)` steps: ten to hoist the constants and guard the loop
once, then five instructions and one branch per step. The lineage, newest
first:

| walk | per digit | why it was replaced |
|---|---|---|
| rotated loop | `10 + 6 (7 - x)` | current |
| header-guarded loop | `10 + 7 (7 - x)` | a branch *and* a jump per step |
| copy through `OUT` | `10 + 11 (7 - x)` | copied the digest into the payload slot |
| M3 walk | `3 + 20 (7 - x)` | also rebuilt the constants inside the loop |

The guard cannot go: digit 7 walks no steps at all, and removing it loses
termination. That candidate is in the reject archive.

## Baseline cycle measurement (M7)

The evaluator (`XmssAsm.runH`) executes the same `verifier` literal the theorem
is about, counting every executed instruction (`steps`), the hash calls among
them (`hashes`), and the synthetic total `ordinary + hashes * hashCost`. Run it
with `scripts/test-differential.sh [hashCost]`.

Every accepting run makes exactly **133 hash calls**, and this is forced by the
scheme rather than by the corpus: 1 encoding, then `7 - x_i` steps for each of
the 42 chains, which is `42 * 7 - 195 = 99` because an accepted encoding's
digits sum to the target 195, then 1 leaf and 32 merkle. The instruction count
varies only with the epoch, through the authentication path's swap branch.

| accepting run | steps | ordinary | hashes |
|---|---|---|---|
| epoch 0 | 3239 | 3106 | 133 |
| epoch 1 | 3242 | 3109 | 133 |
| epoch 2^31 | 3242 | 3109 | 133 |
| epoch 2^32-1 | 3335 | 3202 | 133 |
| random epochs | 3278-3287 | 3145-3154 | 133 |

Rejecting runs cost between 47 steps (a padding bit set in the encoding digest,
which stops before any chain work) and 3335 steps (a wrong root, which does all
the work and fails the final compare).

Per region, on the artifact:

| region | steps | hashes |
|---|---|---|
| init (parameter, payload, encoding hash) | 43 | 1 |
| decode, accepting | 222 | 0 |
| decode, padding reject | 4-6 | 0 |
| 42 chain walks, accepting (digits sum to 195) | 1858 | 99 |
| 42 chain walks, region test with random digits | 2164 | 150 |
| leaf | 16 | 1 |
| authentication path | 1090-1186 | 32 |
| final compare | 9-11 | 0 |

Synthetic totals for the epoch-0 accepting run: 3239 at `hashCost = 1`, 16406
at 100, 69606 at 500. The hash is the dominant cost for any realistic
`hashCost`, which is why the count is fixed at 133 and the optimization work in
M8 is about the 3106 ordinary instructions.

## The optimization contract (M8)

From M8.a on, `main` is the single best-known artifact and Git history is the
leaderboard. A candidate is a patch to that one program, never a second
`Program` beside it.

### The score

```
m = (OTS_steps, XMSS_epmax_steps)      lexicographic

primary    OTS_steps          on an accepting path
secondary  XMSS_steps         on fixture valid-epmax
constraint hashes_OTS  = 101
           hashes_XMSS = 133
           E1 + E2 + E3 pass, xmss_verify_correct holds
```

`gate pass` is `m <= baseline`; `new record` is `m < baseline`. A gate pass at
`m == baseline` is allowed -- a refactor or a proof cleanup should be landable
-- and does not move the scoreboard. `m > baseline` fails the gate even when
the theorem holds. Only a record may be called an improvement.

**Hash counts are an exact pin, not a score term.** A candidate that queries
the oracle fewer times is computing something else. Extra queries can still
satisfy `VerifierCorrect`; they fail the gate anyway. `hashCost` stays a
reporting parameter: among candidates that meet the pin it cannot change the
ranking.

### What "really good" would look like

`bench/baseline.txt` carries `TARGET_OTS_STEPS=512`: a stretch target, not a
gate condition. The gate is `m <= baseline` and stays that way; the target is
a marker to aim at, and the gate prints the distance to it.

It is a hard target. The OTS path is 2139 steps today: 43 init, 222 decode,
1858 for the 42 chain walks, 16 leaf. Inside those 1858 are 42 x 20 of
chain-loop overhead (load 9, store 10, branch 1), 42 x 10 of walk prologue,
99 x 5 of per-step work, 99 hash `ECALL`s and 4 for the loop header. Two parts
of the 512 are close to forced: the 101 hash `ECALL`s on the OTS path cannot
go, because the hash count is an equality pin, and each chain step has to
write a different tweak word, so roughly one store per step. That is about 200
before any other work, leaving ~310 for reading 42 chain values, extracting
and target-sum-checking 42 digits, the leaf payload and all loop control --
against 222 for `decode` alone.

So reaching it needs more than the `chainWalk` search space: `decode` and the
chain load/store overhead have to come down, and the per-step work has to
approach the `ECALL`-plus-one-store floor. Opening those regions is a separate
decision. The stopping points and the hash pin stay frozen either way.

**Not in the score:** reject-path cost, static instruction count, wall time,
proof-check latency, input compression. Reject fixtures are a termination and
fuel filter. Size is a tie-break at most. Proof-check time is recorded and
budgeted, as an engineering constraint on autoresearch throughput, never as
part of the verifier's performance.

### The stopping points

OTS is init + decode + 42 WOTS chains + leaf. Its stopping point is the
**semantic** cut: after the leaf hash, before the first authentication
instruction. `idxAuth` is the index that names that boundary today, but it is
`idxLeaf + leaf.length` and therefore moves whenever a region's length moves,
which a candidate is free to do. What is immutable is which work falls on
each side. A candidate must not push work past the cut to shrink `OTS_steps`.

`OTS_steps` is the same on every accepting fixture for this program, because
target sum 195 forces 99 remaining chain hashes. That is a property of the
program, not of the metric: a digit-dependent fast path would break it and
leave "OTS steps on an accepting path" undefined. The gate therefore asserts
it (`OTS_STEPS_DISTINCT = 1`), which is why no held-out corpus is needed.

XMSS is the full run on `valid-epmax`. That fixture is the worst case as a
**theorem**, not an observation: `XmssAsm.Regions.AuthCost` proves

```
authSteps ep = 1090 + 3 * popcount32 ep
```

with `popcount32 ep <= 32` and equality only at `ep = 2^32 - 1`
(`authSteps_lt_of_ne`). The authentication path branches on exactly one thing,
bit `L` of the epoch, which orders the two children in the merkle payload: 34
steps per level with the bit clear, 37 with it set. `XmssAsmTests.Cost` checks
the theorem against the interpreter on every accepting fixture, so a proof and
a measurement that disagree fail the suite.

### The accept gate

`scripts/accept.sh` is the only path onto `main`. In order:

1. **statement integrity** -- `lake env ./.lake/build/bin/statementpin` prints
   the elaborated form of the frozen vocabulary (the statement, the input
   representation, the layout, the hash-oracle semantics; see
   `XmssAsmTools/StatementPin.lean`) and its hash must match
   `bench/statement.sha256`. This is first because a weakened statement --
   an added hypothesis, a dropped conjunct, a widened frame -- builds cleanly,
   passes the axiom sweep, passes every fixture, and scores better. Nothing
   else in the list catches it. `verifier`, `verifierCode` and the region
   indices are deliberately *not* pinned: those are what a candidate changes;
2. `lake build`, under a wall-clock budget (default 600s,
   `ACCEPT_BUILD_BUDGET`); exceeding it is a reject, not a slow pass, and
   warnings in our own modules are a reject too;
3. `scripts/check-axioms.sh` and `scripts/check-forbidden-tactics.sh`;
4. `scripts/test-differential.sh`;
5. the exact hash pin, `OTS_STEPS_DISTINCT = 1`, and an unchanged corpus size;
6. `lake exe bench` against `bench/baseline.txt`, with proof-check seconds
   reported;
7. the verdict: non-zero on any failure above or on `m > baseline`, zero on a
   gate pass, and `--record` writes the baseline only on a record.

### The autoresearch harness

`scripts/autoresearch.sh` is the one command that judges a candidate patch to
the chain walk. Three tiers, and the split is the point.

1. **The mutation boundary**, `scripts/check-mutation-boundary.sh`. A
   mechanical classification of the candidate's diff into allowed, repair and
   denied. Allowed is the designated region and what moves with it:
   `XmssAsm/Program/Verifier.lean` (the program, its length, the branch
   offsets and the indices stated relative to that length),
   `XmssAsm/Regions/Chain.lean`, `XmssAsm/Regions/Common.lean` and
   `XmssAsm/Machine/Sym.lean` (whose simp set names the offset lemmas).
   Denied is everything frozen: the statements, the specification, the
   representation, the machine and oracle semantics, the benchmark
   definitions, the fixture corpus, the baseline, the gate scripts and the
   toolchain pins. Anything else is *repair above the region*: permitted --
   the Lean kernel is the trust boundary, not the file list -- but reported,
   because insulation is the iteration goal. This is checked first because
   lowering a number in the baseline file is cheaper than weakening a proof,
   and the statement pin does not look at the baseline.
2. **The inner filter**, `lake exe filter`. The interpreter only: the chain
   walk in isolation for every digit against `Concrete.recoverChain`, the
   whole fixture corpus end to end, the hash pin, the score. It imports no
   region proof, so it builds and runs while the candidate's proof is still
   broken, and it rejects a wrong walk in about ten seconds. It is not a
   merge gate. A green filter on a candidate whose `chainWalk_correct` does
   not close is a reject.
3. **The accept gate**, `scripts/accept.sh`, as above.

A new record writes `bench/records/<when>-ots<n>-xmss<n>.txt`: the commit,
whether the tree was dirty and if so the hash of its diff, the baseline it
beat, the metric dump, the proof-check seconds, the statement-pin hash, and
the measured program as an instruction listing. That is enough to reproduce
the measurement from what is written down.

The search space is `chainWalk` only. Restricting the code search keeps
failures local and interpretable and avoids conflating optimizer quality with
whole-program proof architecture. Other regions stay closed until this loop
has been run and reviewed.

### Frozen; and off limits to a candidate

Frozen (changing one is out of spec, not an optimization): the same canonical
`Program` is proved and measured; the `VerifierCorrect` statement; the machine
and input representation; the hash-oracle semantics; the benchmark inputs and
stopping points; the 101/133 hash pin; and the rule that only `m < baseline`
moves the baseline.

Off limits as *candidate material*: `bench/baseline.txt`,
`bench/statement.sha256`, `scripts/accept.sh`, `scripts/check-axioms.sh`,
`scripts/check-forbidden-tactics.sh`, `scripts/test-differential.sh`, and the
fixture corpus. Editing a number in the baseline is cheaper than weakening a
proof, and step 6 writes to that file, so a denylist protecting the theorem
but not the scoreboard is the wrong denylist. Only a human, in a separate
commit, changes the gate or the corpus.

### The reject archive

`XmssAsmTests/Rejects.lean` keeps candidates that failed for a reason worth
remembering, as an instruction list plus the failure they are expected to
produce, and the differential suite asserts each still fails that way. The
no-alternates rule bans a live alternate `Program` a caller could select; it
does not ban recording what went wrong. Nothing outside that file refers to
these lists and none is reachable from `verifier`.

The entry that earns the archive its keep is `shortBound`: a chain bound of
`8 i + 6` instead of `8 i + 7`, which stops each chain one step early. It is
*faster on the score* -- 3209 steps against 3434 on `valid-epmax` -- and
wrong. No step count rejects it. Only the exact hash pin does, which is why
the pin is an equality rather than a bound. The other two entries record a
lost exit test (the fuel filter's job) and a hoist of the position-dependent
tweak store out of the loop (the differential suite's job).

If a recorded reject ever *passes*, the suite fails: either the archive is
stale, or something changed that makes the candidate viable, and it should be
judged by the accept gate rather than left sitting here.

**Proof repair is always permitted**, including of the affected region's proof
file. A land is valid only if the repaired proofs re-establish the *same*
local contracts and the *unchanged* `xmss_verify_correct` for the exact
`Program` the evaluator measured. A green differential suite is never a
substitute for that theorem, and landing with `sorry` is out of spec.

There is no theorem that a given `Program` is optimal. The loop is
best-so-far; a lower bound is a different project.

## Adversarial review of the statement (M1 acceptance)

*Over-strong preconditions?*

* `s.code = verifierCode` fixes the whole code map. It is the "program loaded"
  condition; it excludes embedding the verifier in a larger image, which is a
  backend concern outside scope. Relaxing to `ProgramAt` is a mechanical
  generalisation of the fetch lemmas, not a design change.
* `Represents` asks only for the encodings of the four inputs at their
  addresses. The epoch doubleword must equal `ep.val` exactly (high 32 bits
  zero); anything else is a different number and the tweak would differ, so
  this is the representation, not a restriction.
* Nothing is assumed about scratch memory, registers, or host-I/O fields; the
  result therefore cannot depend on them, and neither can termination.

*Under-specified outputs?*

* The result register and its two values are fixed; halting is pinned to the
  `HALT` syscall (`SyscallHalted`), not to "cannot step", so a trap does not
  satisfy the theorem (`Decomp` README, "Observations").
* The frame names every field of `MachineState`. The registers in `CLOB` and
  the scratch region may hold anything afterwards; the theorem says nothing
  about them beyond `x10`, and is not meant to.
* The hash oracle is universally quantified. A program that calls `H` on the
  wrong bytes, skips a call, or fabricates a digest cannot satisfy the equation
  for every `H`; a program that calls `H` *more* often can, and is caught by
  the benchmark rather than the theorem.
* `stepH` traps on an out-of-range hash call, so termination forces every
  call's buffers to be valid memory.

*What an incorrect program could still do while passing both gates?* It could
be slow, or compute the right answer by a different route (e.g. a different
layout of the same hash inputs). Both are permitted; the benchmark ranks them.
