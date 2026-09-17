# PLAN

The work queue and the open decisions. **Start here.** `README.md` is the
contract; this file is what has not been decided or done yet. Nothing here is
frozen.

Dates are absolute. Today is 2026-09-15; the repository is a scaffold.

---

## Where this is

Scaffolded, not started. The four dependencies are pinned on one toolchain
(Lean v4.33.0, Mathlib `db584cd6`), the axiom and forbidden-tactic gates are in
place, and `XmssAsm/Smoke.lean` / `XmssAsm/Spec.lean` check that the machine
side and the spec side are both reachable from one package. No code, no
theorem.

---

## Open decisions (need Derek)

Ordered by how much they change the shape of the work. Each records the
options seen and, where there is one, a recommendation.

### D1. What is `H`? — hash oracle as an external call, or BLAKE2s in RV64IM

The spec is oracle-parametric: `Concrete.verify` lives in any `m` with
`HasQuery HashSpec m` and never names a hash. leanVM's Rust fixes `H` to
BLAKE2s-256; a verification is a constant 144 compressions.

- **(a) Keep `H` external.** Implement `verify` with each hash call as a call to
  a fixed convention (an `ecall`, or a `JAL` to a symbol left abstract), and
  prove the code correct **for every `H` that answers those calls** — a
  statement with the same abstraction as the spec, and no BLAKE2s to write or
  verify. A BLAKE2s implementation is then a separate, later module and a
  separate theorem, composed by instantiation. Neither SP1's nor ZisK's
  precompile set in `riscv-zkvm` has BLAKE2s, so an `ecall` version would be
  a *modelling* choice, not a real accelerator.
- **(b) BLAKE2s in RV64IM.** Hand-written compression function (10 rounds × 8
  `G`, ≈1.1k instructions unrolled, or a loop), verified against a Lean
  BLAKE2s (RFC 7693) that also has to be written — there is none in Mathlib —
  and validated against RFC vectors. The theorem then says the code computes
  `verify` at `H := blake2s`, via `evalWithAnswerFn` as `precomputedSecretKey`
  already does in `Scheme.lean`.

*Recommendation:* (a) first, (b) as its own milestone. (a) is where every
proof about the verifier's structure lives and it is independent of the hash;
(b) is a self-contained crypto-primitive proof of a different character.

ANSWER: (a)

### D2. Which backend and I/O ABI?

`riscv-zkvm` has SP1 (`ecall` with `HINT_LEN`/`HINT_READ`/`COMMIT`/`HALT`) and
ZisK (input buffer at `0x80000000`, `csrs` accelerators). `riscv-decomp`'s
leaves, regions and syscalls are furthest along for **SP1**, and `zip-2005-asm`
is an SP1 guest. A third option is **no ABI**: state the theorem over a
machine whose memory already holds the inputs, and leave loading to a
separate, evaluated fact (the shape `Decomp` recommends anyway).

*Recommendation:* no ABI for the correctness theorem; SP1 for the runnable
image, when there is one. Confirm the intended prover.

ANSWER: no ABI, SP1 for the runnable image is fine

### D3. Where does the code come from?

- **(a) Written in Lean**, evm-asm style: `Program` literals produced by Lean
  macros, proved by construction with `cpsTripleWithin`/WP, or evm-asm's
  proof-first "DCode" derivations.
- **(b) Compiled**, then decompiled: build leanVM's Rust verifier (or a C one)
  to an ELF, transpile with `elf2lean`, and prove the binary with
  `riscv-decomp` the way `zip-2005-asm` does.

The README says "in the style of evm-asm", which is (a). Under (a) every loop
has a **constant** trip count (42 chains, ≤ 7 steps each and exactly 99 in
total by the target sum, 32 levels), so a bounded `cpsTripleWithin N` with a
literal `N` is expressible and Myreen's fuel-free rules are a convenience, not
a necessity. Under (b) they are a necessity.

*Recommendation:* (a). Decide whether the top-level judgement is `cpsTotal`
(riscv-decomp) or `cpsTripleWithin` (riscv-zkvm); the former composes with
`lean-refine`'s bridge precedent, the latter gives a cycle bound for free.

ANSWER: (a)

### D4. Input layout

`Concrete.verify` takes `PublicKey`, `Epoch`, `Message`, `Signature` as Lean
values. The code takes bytes. Options: leanVM's SSZ layout
(`crates/xmss/src/ssz_serialization.rs`; signature is
`24 ∥ 42·16 ∥ 32·16` bytes), or a layout chosen here (e.g. 8-byte-aligned
fields) with the SSZ decoding as a separate fact.

*Recommendation:* our own aligned layout for the first theorem; SSZ later.

ANSWER: 

### D5. Statement shape

Soundness only (**if** the code accepts **then** `verify = true`), or the full
`iff` (also completeness: honest signatures are accepted), plus termination and
a frame (nothing else in memory changes). `zip-2005-asm` proves soundness only
because its guest is a decision procedure over a statement; here the spec is a
function, so the `iff` is the natural target.

*Recommendation:* the full `iff` with termination; it is what "implements
`verify`" means.



### D6. Is L3 (lean-refine) worth it here?

The abstract algorithm *is* `verify`; there is no separate abstract program to
write. What L3 would buy is **data refinement**: `Fin 42 → Digest` and
`Fin 32 → Digest` versus byte regions, `Encoding` versus 42 three-bit digits
read out of a 16-byte digest. That coupling is real but small. The alternative
is to state it directly as separation-logic assertions (`evmWordIs`-style
"these 16 bytes encode this `Digest`") and skip the monad.

*Recommendation:* defer. Build the first chain-walk proof with assertions
only; adopt `Refine` if the coupling starts being restated per function.

---

## Risks recorded

### R1. `XmssSecurity.Scheme` against VCVio `3ecd5523` · RESOLVED 2026-09-15

leanVM pins VCVio `cbd4144` (Lean v4.31). We require VCVio's first v4.33.0
commit so that the spec shares a toolchain with the machine. **`Scheme.lean`
elaborates against it unchanged** (first build, 2026-09-15), so there is no
toolchain split to reconcile. What remains: only `Scheme` has been checked,
not `Statement` or the proof tree, and a leanVM PR bumping `formal/xmss` to
v4.33 would make this the upstream state rather than an override. Every
`lake update` re-tests it.

### R4. Lake pin precedence

For a package no require names, Lake takes the revision from the manifest of
the LAST dependency that mentions it. The require order in `lakefile.toml`
(`mathlib` last, `VCVio` after `xmss-security`) is load-bearing; the first
attempt inherited Lean-4.31-era Batteries from the spec and failed to compile.
Any new require goes BEFORE `xmss-security`.

### R2. Legacy files at the join

`lean-refine` and `xmss-security` are not `module`s, so the root, `Smoke`,
`Spec` and the eventual bridge are legacy files. Cost: their reverse-import
cone re-elaborates on every edit. Lift when both upstreams migrate; a
`lean-refine` migration is small (five files, Mathlib-only).

### R3. `riscv-zkvm` at a branch, not a tag

Forced by `riscv-decomp`. Every `lake update` is a dependency bump; the
manifest sha is the pin.

---

## Milestones (proposed, pending D1–D6)

| id | what | acceptance |
|---|---|---|
| **M0** | this scaffold builds warning-free; both gates pass | `lake build`, `scripts/check-*.sh` green |
| **M1** | the statement: `xmss_verify_correct`, stated with `sorry`, naming the code, the layout assertions and `Concrete.verify` at the chosen `H` | reviewed statement, adversarial pass recorded |
| **M2** | tweak and payload construction: `tweakableHashInput` bytes laid out in memory, proved | one triple per `HashDomain` constructor |
| **M3** | one chain walk (`recoverChain`) proved | a loop over ≤ 7 hash calls |
| **M4** | all 42 chains + leaf hash (`recoverEndpoints`, `leafHash`) | composition of M3 |
| **M5** | `TargetSum.decodeDigest`: digit extraction, padding bits, sum = 195 | bit-level proof |
| **M6** | authentication path (`authenticationRoot`, 32 levels, ordering by epoch bit) | loop proof |
| **M7** | `verify` end to end, at abstract `H` | M1's `sorry` discharged |
| **M8** | BLAKE2s-256 in RV64IM against a Lean RFC 7693 spec; instantiate M7 | vectors pass; composed theorem |
| **M9** | runnable image on the chosen backend, loaded-state fact by evaluation | `riscv-zkvm-run` accepts a leanVM-generated signature |

M2–M7 are `verify` read bottom-up; each maps to one definition in
`Scheme.lean`.

---

## Done

- 2026-09-15 — **M0**: scaffold builds (2834 jobs, zero warnings), both gates
  pass, `XmssSecurity.Scheme` confirmed to elaborate on Lean v4.33.0 / VCVio
  `3ecd5523`. Lakefile with pinned deps on one toolchain, module / legacy
  split, axiom gate, forbidden-tactic gate, README, this file. Not committed.
