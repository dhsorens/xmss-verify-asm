# A Formally Verified XMSS Verifier in RV Assembly, in Lean

Reference links:
- [RV](https://github.com/Verified-zkEVM/riscv-zkvm)
- [Myreen-style decompilation logic](https://github.com/dhsorens/riscv-decomp)
- [The Spec](https://github.com/leanEthereum/leanVM/tree/main/formal/xmss/XmssSecurity)
    - Scheme.lean is the spec, verified to be true wrt the property in Statement.lean
- [Refinement calculus](https://github.com/dhsorens/lean-refine)
- [evm-asm](https://github.com/Verified-zkEVM/evm-asm)

Goal:
in the style of evm-asm, maybe using the refinement calculus and/or myreen decompilation (if useful!), get a risc-v bytecode implementation of the xmss verifier (defined in the spec above) which is proved correct wrt its Lean spec

---

## Status

**M1-M8 complete: the verifier is proved, and optimization is gated.**

```
theorem xmss_verify_correct (H : HashInput → HashOutput) : VerifierCorrect H
```

The artifact is `XmssAsm/Program/Verifier.lean`, 179 RV64IM instructions. The
theorem (`XmssAsm/Verify.lean`) says that for every hash oracle `H`, starting
from any machine state whose memory represents `(pk, ep, msg, sig)` with the
program loaded at `CODE_BASE`, execution terminates in a halted state whose
`a0` is `Concrete.verify pk ep msg sig` evaluated at `H`, having written
nothing outside the scratch area. It rests on `propext`, `Classical.choice`
and `Quot.sound` only.

The proof is six region contracts composed with `Runs.bind`: init, decode,
the 42-chain loop, leaf, the 32-level authentication path, and the final
compare. A chain-walk change touches four definitions -- the program, its
length, one branch offset and one theorem -- and no proof above the region.

Step counts are theorems too where they can be: the authentication path costs
`1090 + 3 * popcount32 ep` steps (`XmssAsm/Regions/AuthCost.lean`), so the
worst-case accepting epoch is `2^32 - 1` by proof rather than by sampling.

Independently of the proof, the program is executed by an RV interpreter and
compared with the specification on 104 end-to-end fixtures and 450 component
cases (`scripts/test-differential.sh`), all passing.

An accepting verification costs 3338 virtual cycles at epoch 0 and 3434 at the
worst-case epoch, of which 2238 are the one-time signature (init, decode, 42
WOTS chains, leaf); 133 abstract hash calls either way. `scripts/accept.sh`
judges a change against `bench/baseline.txt`. `PLAN.md` is the work queue; M9
(the autoresearch harness) is what remains.

## The stack

Same shape as [`zip-2005-asm`](https://github.com/dhsorens/zip-2005-asm), with
the spec swapped and, unlike there, one toolchain for both halves from day one.

| layer | what | where | status |
|---|---|---|---|
| **L4** spec | `XmssSecurity.Concrete.verify`: `Ver(pk, ep, m, σ)` in a monad with a hash oracle | leanVM `formal/xmss`, pinned | upstream, imported verbatim |
| **L3** algorithm | the verifier in `Nres`, its correctness, data refinement `⇓R` to a byte/limb representation | `lean-refine`; instance here | calculus upstream, **no instance** |
| **L2** decompilation | RV64 code regions as tail-recursive functions + certificates | `riscv-decomp`; instance here | framework upstream, **no instance** |
| **L1** program logic | separation-logic triples over the RV64 `Stepper` | `riscv-zkvm` / `riscv-decomp` | upstream |
| **L0** machine | `decode` / `stepOn`, RV64IM, SP1 and ZisK backends | `riscv-zkvm` | upstream, trusted |
| code | the RV64IM program itself | `XmssAsm/` | **none yet** |

The join, `hnrAsm`-style, that lands an L3 refinement on an L2 `cpsTotal`
belongs here (it names both a machine and a refinement, so neither dependency
can host it). `zip-2005-asm/RefineAsm/Bridge.lean` is the precedent.

## What the spec asks for

`XmssSecurity.Scheme` (448 lines) fixes the instance: 128-bit digests,
`v = 42` chains of `w = 3` bits with target sum `T = 195`, tree height `h = 32`,
16-byte tweaks `0 ∥ tag ∥ 0 ∥ 0 ∥ position ∥ 0⁴ ∥ epoch` (little-endian
fields), and `Th(P, tw, M) = Truncate₁₂₈(H(tw ∥ P ∥ M))` for a random oracle
`H : bytes* → bytes³²`. `Concrete.verify` is: hash the encoding, decode the
target-sum digits (both padding bits clear, digit sum 195), walk the 42 chains
the remaining `7 − xᵢ` steps each, hash the 42 endpoints into the leaf, fold
the 32 authentication nodes to the root, compare.

The spec is **oracle-parametric**: `verify` lives in any `m` with
`HasQuery HashSpec m`. It never names a hash. leanVM's Rust fixes `H` to
**BLAKE2s-256** (`crates/primitives/src/hash.rs`, `crates/xmss/src/hash.rs`),
and a full verification is a constant **144 compressions** (2 encoding + 99
chain + 11 leaf + 32 Merkle). An implementation has to pick a concrete `H`, and
the correctness statement is then about `verify` instantiated at that `H`; the
random-oracle security theorem stays upstream and is not this project's to
re-prove. Which `H`, and whether BLAKE2s is implemented in RV64IM here or
comes from a precompile, is an open decision (`PLAN.md`).

## Layout

```
lakefile.toml             pins; comments say why each dependency and revision
XmssAsm.lean              legacy root (see "module system" below)
XmssAsm/Upstream.lean     module-system hub for the machine side (Decomp → riscv-zkvm)
XmssAsm/Machine/          hash-oracle stepper, layout, symbolic-execution tactics, evaluator
XmssAsm/Program/          the verifier as Program literals (the artifact)
XmssAsm/Spec/             the upstream spec evaluated under a fixed oracle; byte lemmas
XmssAsm/Represent.lean    memory represents (pk, ep, msg, sig); initState
XmssAsm/Contract.lean     the theorem statement VerifierCorrect
XmssAsm/Regions/          region contracts and their machine proofs
XmssAsm/Smoke.lean        wiring check: a Program, cpsTotal and Nres all in scope
XmssAsm/Spec.lean         imports XmssSecurity.Scheme and pins the names the bridge will use
XmssAsmTests/             test hash, fixtures, differential harness (not trusted)
XmssAsmTools/             the axiom gate and the statement pin (not imported by any theorem)
scripts/                  check-axioms.sh, check-forbidden-tactics.sh, test-differential.sh, accept.sh
bench/                    the committed baseline and statement pin (the scoreboard)
docs/CONTRACT.md          the contract, layout, cost model, optimization contract, adversarial review
PLAN.md                   the work queue and open decisions
AGENTS.md                 standing rules
```

## Build

```bash
lake exe cache get        # Mathlib oleans; without it, an hour
lake build                # XmssAsm + XmssAsmTools + XmssAsmTests
scripts/check-axioms.sh
scripts/check-forbidden-tactics.sh
scripts/test-differential.sh
```

One command judges a change to the verifier program end to end:

```bash
scripts/accept.sh         # statement pin, proofs, gates, tests, hash pin, score
```

It exits 0 on a gate pass and 1 on a reject, and prints the score against
`bench/baseline.txt`. For a candidate from an untrusted optimizer, the command
is one level up:

```bash
scripts/autoresearch.sh   # mutation boundary, cheap filter, then the gate
```

`lake exe filter` is the cheap tier on its own (the interpreter, no proofs, so
it rejects a wrong chain walk in seconds), `lake exe bench` the metric dump the
gate consumes, and `lake exe cycles` the region-by-region report. See "The
optimization contract" in `docs/CONTRACT.md` for what is frozen, what is off
limits to a candidate, and the difference between a gate pass and a new
record.

The first build also compiles `VCVio` and `XmssSecurity.Scheme` from source
(no release oleans); `riscv-zkvm` builds from source too, but its import
closure here excludes the generated Sail tree, so that part is fast.

## Dependencies and the toolchain

Everything is Lean **v4.33.0** and Mathlib **v4.33.0** (`db584cd6`). That took
one non-obvious choice: leanVM pins `VCVio` at a Lean v4.31 commit, and this
project instead requires VCVio's first v4.33.0 commit (`3ecd5523`, 2026-08-21),
whose Mathlib pin coincides with `lean-refine`'s. Lake takes the root's revision
of a package over a dependency's, so `xmss-security` is compiled against the
newer VCVio, and `Scheme.lean` elaborates against it unchanged (checked
2026-09-15; re-checked by every build). Had it not, the fallback was
`zip-2005-asm`'s `spec/` sub-package on the upstream toolchain, at the cost of
a split to reconcile before the bridging theorem could be stated.

`riscv-zkvm` is required at `sp1-backend`, not a tag, because `riscv-decomp`
requires that branch and Lake keeps one revision per package.

**The order of the `[[require]]` blocks matters.** For a package no require
names directly (Batteries, Aesop, Qq, PolyFun, ...) Lake takes the revision
from the manifest of the *last* dependency that mentions it. `mathlib` is
therefore last, so the Mathlib cache matches, and `VCVio` is after
`xmss-security`, so VCVio's PolyFun beats the spec package's older one. The
first scaffold attempt had `xmss-security` last and inherited a Lean-4.31-era
Batteries that does not compile on 4.33.

## Module system

`riscv-zkvm` and `riscv-decomp` are Lean `module`s; `lean-refine` and
`xmss-security` are legacy packages, and a `module` cannot import a legacy
file. So `XmssAsm/Upstream.lean` is a module (machine side only) and anything
that names `Refine.*` or `XmssSecurity.*`, including the root, is a legacy
file. The bridging theorem will be legacy until both upstreams migrate.

## Trust

Target: every declaration under `XmssAsm` rests on `propext`,
`Classical.choice`, `Quot.sound` and nothing else; `scripts/check-axioms.sh`
reads what the kernel recorded, `scripts/check-forbidden-tactics.sh` keeps
`native_decide` and `bv_decide` out of the source. Not reduced by anything
here: the RV64 model and its backends, Lean, Mathlib, and the security theorem
upstream (which is about the random-oracle scheme, not about any concrete `H`).

## Licence

None yet.
