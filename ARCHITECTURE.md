# ARCHITECTURE

How this repository is put together, and why. **Start here**, then
`docs/CONTRACT.md` for the contract itself.

`README.md` is the summary and the current numbers. `AGENTS.md` is the standing
rules in short form. `AUTORESEARCH.md` is the prompt for pointing an agent at
the optimization loop. Nothing in any of them is frozen; the frozen things are
listed under [What is frozen](#what-is-frozen) below.

## What the result is

One RV64IM program, 179 instructions, and one theorem that it implements
leanVM's XMSS verifier:

```lean
theorem xmss_verify_correct (H : HashInput → HashOutput) : VerifierCorrect H
```

For every hash oracle, from every machine state whose memory represents
`(pk, ep, msg, sig)` with the program loaded at `CODE_BASE`, execution
terminates in a halted state whose `a0` is `Concrete.verify pk ep msg sig`
evaluated at `H`, having written nothing outside the scratch area. It rests on
`propext`, `Classical.choice` and `Quot.sound` and nothing else.

An accepting run costs 3239 virtual cycles at epoch 0 and 3335 at the
worst-case epoch, of which 2139 are the one-time signature; 133 abstract hash
calls either way.

## Where to start

| you want to | read |
|---|---|
| know what the theorem promises | `docs/CONTRACT.md` |
| find the program | `XmssAsm/Program/Verifier.lean` |
| find the theorem | `XmssAsm/Verify.lean`, statement in `XmssAsm/Contract.lean` |
| understand a region proof | `XmssAsm/Regions/Chain.lean` (the smallest), then `XmssAsm/Machine/Sym.lean` for the tactics |
| change the chain walk | `AUTORESEARCH.md`, then `docs/CONTRACT.md` § "The optimization contract" |
| judge a change | `scripts/accept.sh` |

## Repository structure

```
XmssAsm/Upstream.lean     module-system hub for the machine side (Decomp → riscv-zkvm)
XmssAsm/Machine/
  Hash.lean               the hash ECALL's semantics; Reaches, Runs
  Layout.lean             memory layout and the word-level encodings
  Cost.lean               RunsN: the same execution with the step count in the statement
  Sym.lean                symbolic-execution tactics over a flat state literal
  Eval.lean               the interpreter and the cycle counter
XmssAsm/Program/
  Verifier.lean           the artifact: the program, its region indices and branch offsets
XmssAsm/Spec/
  Eval.lean               the upstream verifier evaluated under a fixed answer function
  Bytes.lean              the byte-level bridge: spec bytes = machine doublewords
  Decode.lean             target-sum decoding at the bit level
XmssAsm/Spec.lean         rename tripwire: names every upstream constant the proof uses
XmssAsm/Represent.lean    Represents, initState, and the proof they agree
XmssAsm/Contract.lean     the statement: VerifierCorrect
XmssAsm/Regions/          one contract and machine proof per region, plus AuthCost
XmssAsm/Verify.lean       the six regions composed: xmss_verify_correct

XmssAsmTests/             test hash, fixtures, region and end-to-end differential
                          suites, the reject archive, the metric dumps. Not trusted,
                          not imported by any theorem
XmssAsmTools/             the axiom gate and the statement pin
scripts/                  the gates
bench/                    the committed baseline, the pins and the records
docs/CONTRACT.md          the contract, cost model, optimization contract, adversarial review
```

The six regions, in execution order, are init, decode, the 42-chain loop, leaf,
the 32-level authentication path, and the final compare. `docs/CONTRACT.md` has
their contracts.

## The decisions

These are settled. They are the shape of the project, not open questions, and
each should only be reopened if implementation experience shows it getting in
the way.

**Pure virtual RV64.** The artifact is a program under `riscv-zkvm`'s RV64IM
model. No SP1 or ZisK backend, no host ABI, no ELF startup convention and no
prover memory map appears in the theorem or the benchmark; inputs are already
in memory when execution begins. Backend integration, if it is ever useful, is
a layer on top that does not disturb the verifier proof.

**The hash is an abstract oracle.** `H : List UInt8 → BitVec 256` is a
parameter of everything, matching `Concrete.verify` upstream. The code reaches
it through one host-neutral `ECALL` convention, and that contract
(`XmssAsm/Machine/Hash.lean`) is the *only* semantics added to the RV64 model.
The proof never needs to know how `H` is implemented, so the theorem holds at
BLAKE2s-256 and every other choice at once. Proving or implementing a concrete
hash is a different problem and a non-goal.

**The RV code is written directly in Lean, as `Program` literals.** The
instruction sequence is the thing being optimized, so it is explicit and
editable rather than compiler output, and the benchmark is not coupled to a
compiler. Hex words are not proof objects. Control flow is small and statically
bounded -- 42 chains, at most 7 steps each, 32 authentication levels, 42 digits
-- which is what makes a handwritten implementation realistic.

**Structured spec inputs are related to memory directly.** `Concrete.verify`
operates on `PublicKey`, `Epoch`, `Message`, `Signature`; the machine operates
on memory. The bridge is one predicate, `Represents`, and nothing more: no
serialization, no SSZ, no frontend parsing, and above all no second Lean
implementation of XMSS. The layout is fixed, doubleword-aligned and chosen for
cheap loads and stores.

**The theorem is full functional equivalence, with termination and a frame.**
Not "if it terminates, the answer is correct" -- termination is inside `Runs`,
which is an existential over a step count, so it is proved for accepting and
rejecting inputs alike. The frame says which memory and registers the verifier
may touch, because an optimizer will otherwise find the unconstrained ones.

**Regions expose contracts; callers consume only the contract.** Each region's
theorem assumes only that its own instructions sit at its own slot (`CodeAt`),
so it says nothing about the rest of the program. The 42-chain loop goes
through `chainWalk_correct` and nothing else about the walk; the authentication
path proves one block contract and composes it 32 times. This is what makes
local optimization possible: a chain-walk change touches the program, its
length, one branch offset and one theorem, and no proof above the region.

That boundary was validated rather than asserted. Two different instruction
sequences were proved against the same chain-walk contract and swapped in both
directions, with four declared edits and zero proof changes each way. `main`
carries one implementation; git history keeps the experiment.

**Proof automation is explicit and local.** `simp only` with a named lemma
list, never a bare `simp`; small region proofs; directional normalization
lemmas. Proof-check latency is an engineering requirement, not a detail: the
optimization loop pays for a full check on every candidate under a wall-clock
budget, so a proof that is correct but slow is an architectural problem.

**Cost is measured on the proved program, and where possible it is a theorem.**
The evaluator runs `stepH H` -- the same transition function the theorem is
stated over -- on the same `verifier` value, and takes no program parameter, so
it cannot be pointed at something the theorem is not about. One virtual cycle
per executed instruction; the hash call costs `hashCost`, default 1. The
benchmark is deliberately backend-independent and does not approximate SP1 or
ZisK proving cost, real CPU latency or accelerator cost. Where a cost can be
proved it is: the authentication path costs `1090 + 3 * popcount32 ep` steps
(`XmssAsm/Regions/AuthCost.lean`), so the worst-case accepting epoch is
`2^32 - 1` by proof rather than by sampling.

**The optimizer is not trusted.** The Lean kernel is the trust boundary, not
the optimizer's reasoning and not its test results. A green differential suite
is never a merge gate.

## Layering rules

- **None of the frameworks live here.** `RiscvZkvm.*`, `Decomp.*` and
  `XmssSecurity.*` arrive under `.lake/packages/`. Read them there; never edit
  them from here. A change is a PR against that repository, then
  `lake update <dep>`.
- Before adding anything abstract, ask which repository owns it. Names a
  machine but not XMSS: `riscv-decomp`. Names XMSS but not a machine: the
  spec's, and if the spec is wrong that is a leanVM issue rather than a local
  patch. Names both: here.
- Keep the layers distinct: spec / machine / region / composition. A theorem
  naming both `Concrete.verify` and `MachineState` outside the bridge means the
  abstraction has collapsed.
- Mathlib: targeted `import Mathlib.<Module>` only, never `import Mathlib`.

**Module system.** `riscv-zkvm` and `riscv-decomp` are Lean `module`s;
`xmss-security` is a legacy package, and a `module` cannot import a legacy
file. So `XmssAsm/Upstream.lean` is a module and re-exports the machine side,
and everything that names `XmssSecurity.*` -- the spec bridge, the region
proofs, `Verify.lean`, the root -- is a legacy file. Do not "fix" this by
copying upstream definitions into a module. It stays until the upstream spec
adopts the module system.

**Dependency pinning.** Everything is Lean v4.33.0 and Mathlib v4.33.0. The
order of the `[[require]]` blocks is load-bearing and the lakefile comments say
why for each one; the short version is that Lake resolves an unnamed transitive
package from the *last* dependency that mentions it, so `mathlib` is last and
`VCVio` is after `xmss-security`. Do not move a pin without saying which one
moved and why.

**The L3/L2 route was considered and not taken.** The original plan was an
`hnrAsm`-style join landing a `lean-refine` refinement on a `riscv-decomp`
`cpsTotal`. What the proof does instead is state a contract per region directly
over the hash-oracle stepper. For a program this size that was the shorter path
and it kept the region boundaries sharper, which is what the optimization loop
needs. `lean-refine` is therefore not a dependency; re-adding it is one
`[[require]]` block if a future L3 layer wants it. `riscv-decomp` stays, for the
`Stepper`, `SyscallHalted` and the loop rules.

## What is frozen

Frozen means changing it is out of spec rather than an optimization: the same
canonical `Program` is proved and measured; the `VerifierCorrect` statement; the
machine and input representation; the hash-oracle semantics; the benchmark
inputs and stopping points; the 101/133 hash pin; and the rule that only a
strict improvement moves the baseline.

Not candidate material at all: `bench/*`, `scripts/*` and the fixture corpus.
Editing a number in the baseline is cheaper than weakening a proof, so the
boundary is enforced mechanically by `scripts/check-mutation-boundary.sh` rather
than trusted, and separate hashes pin the elaborated statements
(`bench/statement.sha256`) and the frozen regions' instruction lists
(`bench/regions.sha256`).

`docs/CONTRACT.md` § "The optimization contract" is the authority on all of
this, including the score and what counts as a record.

## Working on the repo

```bash
lake exe cache get        # Mathlib oleans; without it, an hour
lake build                # must stay warning-free
scripts/accept.sh         # statement pin, proofs, gates, tests, hash pin, score
```

`scripts/accept.sh --no-boundary` is the maintainer form, for a change to the
gate, the corpus or the pin. For a candidate from an untrusted optimizer the
command is `scripts/autoresearch.sh`, which adds the mutation boundary and a
cheap interpreter-only filter in front.

Standing rules, in short: never introduce an `axiom`; unfinished proofs use
`sorry`, which is grep-able and which the gates reject; no `native_decide` or
`bv_decide`; unused hypotheses mean the theorem is not tight, so drop them;
warnings are part of the work, not later cleanup. A green proof of a weak
statement is not progress -- prefer, in order, a real semantic disagreement, a
vacuous or false guarantee, a blind spot in the model or the observation, a
meaningful theorem with an explicit trust base, and an honest unknown.

The symbolic-execution proofs have three failure modes that cost real time;
`AUTORESEARCH.md` § "Proof-repair notes" and the header of
`XmssAsm/Machine/Sym.lean` describe them. The short version: destructure the
`sym_code` fetch facts positionally and expect every index to shift when the
instruction count does; resolve an `if` on a `Fin` projection before `sym_norm`
sees it; and do not rewrite values into the symbolic state ahead of a hash call.

## What still bites

The architectural risks that are live rather than retired.

- **An optimizer will exploit any gap between the theorem and the
  measurement**: specializing to the benchmark inputs, reaching an unmeasured
  path, leaning on state the theorem left unconstrained. The reject archive's
  `shortBound` is the worked example -- a chain bound one step short, faster on
  the score and wrong, caught by the hash pin and by nothing else. Before
  opening a region, ask what incorrect program could still pass both gates.
- **Abstraction is for proofs, not execution.** The proof may reason about
  `recoverChain` abstractly; the evaluator must still execute and count the
  concrete instructions. The hash oracle is the only uninterpreted operation in
  the measurement.
- **Never report "N cycles"** without naming the input and the cost model.
  Reject paths are short and the authentication path depends on the epoch bits.
- **Proof-check latency degrades quietly.** One authentication-path proof went
  from nine seconds to a kernel timeout purely by changing when values were
  rewritten into the symbolic state.
- **There is no lower bound.** The loop is best-so-far. `TARGET_OTS_STEPS=512`
  in `bench/baseline.txt` is a marker, not a gate, and reaching it needs
  regions outside the current search space -- a human decision.

## Non-goals

Proving BLAKE2s; implementing BLAKE2s in RV64; SP1 or ZisK integration; zkVM
proving-cost optimization; host I/O syscalls; frontend protocols; SSZ
compatibility; reproducing leanVM's production serialization; a second Lean
implementation of the XMSS verifier; re-proving the upstream XMSS security
theorem; trusting the optimizer.

Each of these can be layered on later without changing the core verifier
theorem, which is the point of choosing the boundaries above.

## Changelog

Dates are absolute. Git is the detailed record; this is the shape of it.

**2026-09-15** — Scaffold: warning-free build, both trust gates, and
`XmssSecurity.Scheme` elaborating on Lean v4.33.0 against VCVio `3ecd5523`,
which is what put the spec and the machine on one toolchain.

**2026-09-17** — Direction settled (the decisions above). Then, in one day: the
contract fixed; the program, evaluator and 104-fixture harness landing early and
agreeing with the spec, unproved, at 185 instructions; the hash call's semantic
contract and the byte-level bridge; the symbolic-execution engine; the
chain-walk contract proved against *two* instruction sequences and swapped both
ways with four declared edits and no proof change; init, the 42-chain loop and
the leaf; target-sum decoding; the authentication path and the final compare;
and **`xmss_verify_correct`**, the six regions composed with `Runs.bind`.
Baseline OTS 3231, XMSS epmax 4427, static 203.

**2026-09-18** — Optimization. One program on main, the metric and stopping
points frozen, `auth_steps(ep) = 1090 + 3 * popcount32 ep` proved, and the
accept gate installed: OTS 2634, XMSS 3830, static 183. The oracle made to
write the chain digest in place, so the walk never copies it: OTS 2238, XMSS
3434, static 179. Then the autoresearch harness, and through it the rotated
chain loop: **OTS 2139, XMSS 3335**, the current record.

**2026-09-18** — Cleanup: the scaffold-era smoke test and the `lean-refine`
dependency dropped, one unused Mathlib import removed, stale docstrings
corrected, `PLAN.md` retired in favour of this file.
