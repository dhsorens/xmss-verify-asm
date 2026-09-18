# PLAN

The work queue and current design decisions. **Start here.** `README.md` is the repository contract; this file records what remains to be implemented and proved. Nothing here is frozen.

Dates are absolute. Today is 2026-09-18.

---

## Where this is

M1 done (2026-09-17): the contract is fixed (`docs/CONTRACT.md`,
`XmssAsm/Contract.lean`), the hash-oracle stepper, layout, evaluator and the
complete 185-instruction verifier exist, and the unproved program agrees with
`Concrete.verify` on the 104-fixture end-to-end corpus
(`scripts/test-differential.sh`). The correctness theorem is stated
(`VerifierCorrect`) and being proved; M2-M7 are the proof.

M2 done (2026-09-17): the hash call's semantic contract (`stepH_hash`,
`stepH_hash_input`, `hashInputOf_eq`), the byte-level bridge from the spec's
`tweakBytes`/payload bytes to the machine's doublewords
(`XmssAsm/Spec/Bytes.lean`: `tweakBytes_chain/leaf/encoding/merkle`,
`tweakableHashInput_eq`, `encodingPayload_eq`, `nodePayload_eq`,
`leafPayload_eq`, `readWords_digests`), the symbolic-execution engine
(`XmssAsm/Machine/Sym.lean`: `sym_*` steps, `sym_code` fetch facts,
`sym_frame_W`), the evaluator with its cost model (`XmssAsm/Machine/Eval.lean`,
`docs/CONTRACT.md`), and 14 executable bridge checks in `difftest`.

M3 done (2026-09-17): `XmssAsm/Regions/Chain.lean` proves two chain-walk
implementations (`chainWalkA`: reload constants per step, 22 instructions;
`chainWalkB`: constants hoisted, 20 instructions) against one contract
`ChainWalkPre → Runs H s (ChainWalkPost … pcEnd)`: `CUR = recoverChain P ep i x v`,
caller registers kept, `P` untouched, frame `WChain` (tweak, `CUR`, `OUT`),
termination built into `Runs`. Each theorem assumes only `CodeAt C
(addr idxChainWalk) chainWalkX 0`, so the caller-facing theorem
`chainWalk_correct` selects an implementation without touching any proof. The
swap was performed (A→B→A): 4 declared edits (`chainWalk`, `chainWalk_length`,
`bOff_chainsLoop`, `chainWalk_correct`), zero proof changes, build and suite
green. Digits `0..7` are differentially tested for both implementations (336
region cases, frame checked on the whole data layout); cycle counts are in
`docs/CONTRACT.md`. Next: M4 (`Regions/Init.lean`, 42-chain loop, leaf).

M4 done (2026-09-17): `XmssAsm/Regions/Init.lean` (`init_correct`: `P` into
both buffers, encoding payload, encoding hash into `x20`/`x21`),
`XmssAsm/Regions/Chains.lean` (`chains_correct`: the 42-chain loop as
`Runs.loop` over an invariant on the `ENDPTS` slots, each iteration going
through `chainWalk_correct` and nothing else about the walk), and
`XmssAsm/Regions/Leaf.lean` (`leaf_correct`: the 704-byte leaf hash via
`readWords_digests`/`leafPayload_eq`). The A→B→A swap was repeated with the
chains loop as a real caller: build and suite green, no proof edited. Region
tests: 28 chains/leaf cases on both builds (all-0, all-7 and random digits;
frame checked on the whole data layout). Chains region cycles (steps): A
970 + 20·(hashes), B 1264 + 11·(hashes); leaf 16 steps, 1 hash.

M5 done (2026-09-17): `XmssAsm/Spec/Decode.lean` relates the spec's
`digestEncoding` to the machine's `(half >>> 3k) &&& 7` digits (`digit_lo`,
`digit_hi`), the padding bits to the top bits of the halves (`pad63`,
`pad127`), and the 21-step accumulator to `TargetSum.sum` (`sumTo_21`, via
`Fin.sum_univ_eq_sum_range`/`Finset.sum_range_add`); `decodeDigest` is
characterised case by case. `XmssAsm/Regions/Decode.lean` proves
`decode_correct`: if `decodeDigest d = some enc` the region reaches `idxChains`
with the 42 digits in `DIGITS`, else it halts at the reject stub with `a0 = 0`
(`Rejected`: `SyscallHalted`, `stepH = none`), frame `DIGITS`. 50 decode
region cases per build (sum 195 / 194 / 196, each padding bit, zero, ones,
all-7, random, the valid fixtures' encoding digests). Decode costs 222 steps
on accept, 4/6 on a padding reject, 223 on a sum reject.

M6 done (2026-09-17): `XmssAsm/Regions/Auth.lean` proves `auth_correct`, the
32-level authentication path, as `Runs.loop` over an invariant carrying
`authD H P ep sig leaf L` in `CUR`. Each level selects the child order from
bit `L` of the epoch (`bit_test`: the machine's `(ep >>> L) &&& 1` is
`Nat.testBit`), writes the merkle tweak (`tw0_merkle`, `tw1_node`: the
machine's `ep >>> (L+1)` is `Concrete.nodeIndex`), and hashes through one
shared block contract `authHash_correct` used by both orderings.
`XmssAsm/Regions/Final.lean` proves `final_correct`: the region halts with
`a0 = 1` exactly when `CUR = ROOT`. 22 auth region cases per build (epochs
0, max, 0x55555555, 0xAAAAAAAA, 1, 2^31, random, zero and ones digests), each
checking the root against `authenticationRoot`, the frame, and 32 hash calls.

M7 done (2026-09-17), and with it the goal of this plan. `XmssAsm/Verify.lean`
composes the six region contracts with `Runs.bind` into

    theorem xmss_verify_correct (H : HashInput → HashOutput) : VerifierCorrect H

which discharges the M1 statement: for every hash oracle, every machine state
whose memory `Represents (pk, ep, msg, sig)` with the verifier loaded at
`CODE_BASE`, execution reaches a halted state whose `a0` is
`resultWord (evalH H (Concrete.verify pk ep msg sig))`, with `Frame InScratch`.
Termination is inside `Runs` (it is an existential over a step count), so it is
proved, not assumed. `#print axioms` reports `propext`, `Classical.choice`,
`Quot.sound` and nothing else: no `sorry`, no new trust. `initState_represents`
proves the differential harness builds a state satisfying that precondition
(PLAN E2), and `initState_verify` is the theorem applied to it. Baseline cycle
measurements are in `docs/CONTRACT.md`.

Next is **M8.a**: collapse the M3 dual chain-walk to one program on main
(the hoisted walk, today's B), freeze the OTS / XMSS cost function and
invariants, and install a single accept gate. Then M8.b (overwrite that
artifact only on a strict metric record) and M9 (untrusted agent, same
gate, `chainWalk` plus local proof repair).

The project target is:

> Produce pure RV64 bytecode implementing the XMSS verifier, prove it equivalent to the existing Lean specification, measure its virtual RV cycle count, and make the proof architecture robust enough that the bytecode can be aggressively optimized without rebuilding the high-level proof.

Concrete zkVM deployment, SP1/ZisK integration, and concrete BLAKE2s verification are outside the core scope.

---

## Project objective

This is a backend-independent verified-code optimization challenge.

Given the existing Lean specification of the XMSS verifier:

1. define the machine-memory representation of the verifier's structured inputs;
2. implement the verifier in pure RV64 bytecode;
3. prove the RV64 implementation functionally equivalent to `XmssSecurity.Concrete.verify`;
4. build a deterministic cycle-counting harness;
5. optimize the bytecode for fewer RV cycles while preserving the proof.

The optimization/search process is untrusted. It may propose arbitrary bytecode changes.

Lean is the correctness gate.

A separate deterministic evaluator reports the performance metric.

The desired loop is:

```text
candidate RV bytecode
       |
       +---- Lean proof check ----> correct / rejected
       |
       +---- cycle evaluator -----> measured cost
```

A candidate is useful only if it both passes the proof and improves the chosen cycle metric.

No zkVM backend, concrete hash implementation, frontend protocol, serialization layer, or host ABI is required for the core result.

---

## Architecture

The verifier is deliberately designed around a small set of stable boundaries. These are not pending choices. They define the shape of the project and should only be revisited if implementation experience shows that one of them is getting in the way.

### Pure virtual RV64 execution

The core artifact is a pure RV64 program running under the trusted RISC-V model.

There is no SP1 backend, no ZisK backend, and no host ABI in the main theorem or benchmark.

Inputs are already present in machine memory when execution begins. The verifier runs entirely inside the virtual RV machine and terminates with a boolean result.

The theorem does not depend on:

- host input syscalls;
- output commit APIs;
- ELF startup conventions;
- prover-specific memory maps;
- zkVM accelerators;
- backend-specific execution semantics;
- zkVM proving cost.

For benchmarking, execution is measured using one deterministic backend-independent RV cycle model.

Backend integration, if ever useful, is a separate layer that can be added later without changing the core verifier proof.

### Abstract hash oracle

The verifier remains parametric in the hash function, matching the structure of `Concrete.verify` upstream.

The RV code calls a fixed host-neutral hash interface. The correctness theorem assumes a semantic contract saying that this interface returns `H(input)` and respects its documented memory and register frame.

Conceptually:

```text
RV verifier
    |
    | hash call
    v
HashContract H
    |
    v
abstract oracle H
```

The verifier proof itself never needs to know how `H` is implemented.

There is no concrete BLAKE2s milestone in this project. BLAKE2s matters for leanVM's concrete production instantiation, but proving a cryptographic hash implementation is a separate problem from proving and optimizing the verifier structure.

For benchmarking, an abstract hash call receives a fixed synthetic cost controlled by one parameter.

A reasonable initial convention is:

```text
abstract hash call = 1 virtual cycle
```

The exact value may be changed for sensitivity analysis.

This cost is part of the benchmark definition only. It is not intended to model real hardware, SP1, ZisK, or another zkVM.

### RV code written directly in Lean

The RV program is part of the artifact being optimized, so the implementation is written directly in Lean rather than treated as compiler output.

This keeps the instruction sequence explicit and makes local optimization experiments straightforward.

It also avoids coupling the benchmark to a particular compiler.

The verifier's control flow is small and tightly bounded:

- 42 WOTS chains;
- at most 7 remaining steps in any one chain;
- 99 total chain hash steps when the target-sum condition holds;
- 32 Merkle authentication levels.

That makes a handwritten implementation realistic.

Compiled and decompiled code may still be useful as a comparison point, but it is not the primary implementation path.

### Structured specification inputs represented in RV memory

The authoritative Lean verifier is already `XmssSecurity.Concrete.verify`.

The project should not introduce a second byte-level verifier, a second XMSS implementation, or an independent serialization algorithm.

`Concrete.verify` operates on structured values such as:

```text
PublicKey
Epoch
Message
Signature
```

The RV machine operates on memory.

The bridge between the two is therefore a representation predicate describing when concrete machine memory represents those structured values.

Conceptually:

```text
(pk, ep, msg, sig)
       |
       | representation relation
       v
RV machine memory
       |
       v
RV verifier
```

The top-level theorem should quantify over structured specification inputs and an RV machine state whose memory represents them.

It should then relate the RV result directly to:

```text
Concrete.verify pk ep msg sig
```

The concrete memory layout should be:

- fixed;
- deterministic;
- simple to state as a Lean predicate;
- efficient for RV loads and stores;
- convenient for local reasoning and frame proofs.

An aligned internal layout is preferred if it simplifies the implementation.

Compatibility with leanVM's SSZ representation is not required for the core challenge.

Serialization, SSZ decoding, frontend parsing, and host input loading are separate concerns and remain outside the verified RV program unless the project explicitly expands scope later.

### Full functional equivalence

The target theorem proves full functional equivalence rather than soundness alone.

For every structured input `(pk, ep, msg, sig)` and every machine state satisfying the corresponding memory-representation predicate, RV execution should terminate and return exactly the same boolean as:

```text
Concrete.verify pk ep msg sig
```

Conceptually:

```text
memory represents (pk, ep, msg, sig)
              |
              v
        run RV verifier
              |
              v
result = Concrete.verify pk ep msg sig
```

This includes:

- accepting structured inputs;
- rejecting structured inputs;
- all machine states satisfying the declared representation precondition.

The theorem should also state the relevant frame behavior so that it is explicit which memory and registers the verifier is allowed to modify.

### Reusable verified blocks and composition

Repeated XMSS operations should be implemented as small reusable RV regions, each exposing a stable semantic contract.

These blocks are then composed to form the complete verifier.

The intended hierarchy is approximately:

```text
hashCall
tweakableHashStep

recoverChainStep
recoverChain
recoverEndpoints
leafHash

decodeDigit
decodeDigest

authStep
authenticationRoot

verify
```

The repeated structures are particularly important:

- each WOTS chain repeatedly applies a chain/hash step up to 7 times;
- the verifier applies `recoverChain` across 42 WOTS chains;
- digest decoding extracts 42 three-bit digits;
- authentication-root reconstruction applies essentially the same parent-step operation 32 times.

The proof should establish the semantics of a small repeated block once, then prove bounded composition separately.

For example:

```text
RV recoverChainStep
        |
        | machine proof
        v
recoverChainStep contract
        |
        | bounded repetition
        v
recoverChain contract
        |
        | repeated across 42 chains
        v
recoverEndpoints contract
```

Similarly:

```text
RV authStep
    |
    | machine proof
    v
authStep contract
    |
    | repeated 32 times
    v
authenticationRoot contract
```

Abstraction is for proofs only.

The evaluator must still execute and count the concrete instructions inside every block. Only the explicitly abstract hash operation is given synthetic semantics and cost.

Local optimized implementations may be swapped behind the same semantic contract without requiring callers to change.

### Optimization-resilient proof boundaries

The proof architecture is designed so local bytecode optimizations do not cascade through the entire proof tree.

Important contracts are expected to include:

```text
tweakableHashStep
recoverChainStep
recoverChain
recoverEndpoints
leafHash
decodeDigit
decodeDigest
authStep
authenticationRoot
verify
```

Machine-level proofs establish these contracts.

Higher-level XMSS proofs compose them.

The 42-chain proof should not depend on:

- exact instruction addresses;
- a particular register allocation;
- the precise instruction sequence;
- irrelevant intermediate machine states.

The 32-level authentication proof should similarly consume an `authStep` contract instead of duplicating low-level machine reasoning 32 times.

Repeated structures should be proved by first establishing a one-step or one-block contract, then separately proving bounded composition.

### Automation-first proof style

Proof automation should be designed to survive local implementation changes.

Prefer:

- carefully designed local simp lemmas;
- `simp`;
- `grind`;
- reusable WP or decompilation rules;
- local frame lemmas;
- semantic normalization lemmas;
- small reusable machine contracts.

Avoid long proof scripts tied to a particular sequence of intermediate machine states.

The goal is for Lean to act as a robust correctness gate during optimization, rather than making every small code change require extensive manual proof repair.

### `lean-refine` remains optional

`lean-refine` is not part of the architectural commitment.

Its main potential value is data refinement between abstract XMSS objects and machine-level memory representations.

For example:

```text
Fin 42 -> Digest
```

may need to correspond to a concrete region of machine memory containing 42 encoded values.

If `lean-refine` substantially reduces repeated representation reasoning, use it.

If direct separation-logic predicates and semantic contracts remain simpler, skip it.

The important requirement is the stable refinement boundary, not a particular framework.

### Deterministic virtual-cycle benchmark

Performance is measured independently from correctness.

The program being benchmarked must be exactly the program being proved.

The simplest initial metric is:

```text
1 executed ordinary RV instruction = 1 virtual cycle
```

unless the existing interpreter already exposes a more useful deterministic metric.

Abstract hash calls receive a fixed documented synthetic cost.

The benchmark is intentionally backend-independent. It does not attempt to approximate:

- SP1 proving cost;
- ZisK proving cost;
- real CPU latency;
- cryptographic accelerator cost.

The desired optimization loop is:

```text
candidate RV bytecode
       |
       +---- Lean proof check ----> correct / rejected
       |
       +---- cycle evaluator -----> measured cost
```

The optimizer itself is untrusted.

A candidate **passes the gate** only if it passes the proof, meets the exact hash pin, and does not regress the frozen metric (`m ≤ baseline`). It is a **new record** (and the only case that updates the committed baseline) only if it also strictly improves that metric (`m < baseline`).

---

## Benchmark model

The optimization objective must be explicit and reproducible.

### Ordinary instructions

Every executed ordinary RV instruction contributes according to one fixed virtual cycle model.

For the initial challenge:

```text
1 executed RV instruction = 1 cycle
```

unless the existing interpreter already exposes a more useful deterministic metric.

The metric must remain backend-independent.

### Abstract hash calls

Hashing is axiomatized.

A hash call therefore receives a fixed synthetic benchmark cost.

For example:

```text
abstract hash call = 1 cycle
```

The exact number is configurable, but must be documented and constant across a benchmark comparison.

The purpose is to optimize the verifier logic rather than the hash implementation.

### Artifact identity

The program being measured must be exactly the program being proved.

The benchmark tooling should make it difficult to accidentally:

- prove one bytecode artifact;
- measure another.

Ideally the same Lean `Program` value, generated binary, or canonical byte sequence is consumed by both the proof and cycle evaluator.

---

## Repository constraints

These are known constraints of the current repository and dependency graph.

They are not open design questions, but changes to dependencies or project structure must preserve them.

### C1. VCVio version compatibility

leanVM pins VCVio `cbd4144` on Lean v4.31, while this repository uses Lean v4.33.0.

The repository instead requires VCVio `3ecd5523`, whose Mathlib pin is compatible with the rest of the project. `XmssSecurity.Scheme` currently elaborates against this newer VCVio unchanged.

This was checked on 2026-09-15.

**Agent rule:** after any update to Lean, Mathlib, VCVio, or `xmss-security`, rebuild the imported XMSS specification before doing further work. Do not assume upstream compatibility from version numbers alone.

### C2. Legacy/module-system boundary

`riscv-zkvm` and `riscv-decomp` use Lean modules, while `lean-refine` and `xmss-security` are legacy packages.

A module cannot directly import a legacy file, so code that connects the machine proof to `XmssSecurity.*` must currently live on the legacy side of the boundary.

**Agent rule:** do not restructure imports merely to make the project look cleaner if doing so crosses this boundary. Keep machine-only code in module-compatible files and place the final specification bridge in legacy files until the upstream packages migrate.

### C3. `riscv-zkvm` revision is constrained by `riscv-decomp`

The usable `riscv-zkvm` revision is currently determined by `riscv-decomp`.

The manifest SHA should be treated as the actual pin.

**Agent rule:** treat every `lake update` as a dependency change requiring a clean build and both repository gates. Do not casually move `riscv-zkvm` to another branch or revision independently of `riscv-decomp`.

### C4. Lake dependency ordering is load-bearing

Lake may inherit revisions of transitive dependencies from dependency manifests. The ordering of root `[[require]]` entries therefore affects which versions are selected.

The current ordering is known to produce a compatible Lean v4.33.0 dependency graph.

**Agent rule:** when adding, removing, reordering, or updating dependencies, inspect the resulting manifest and run a clean build. Do not treat `lakefile.toml` ordering as cosmetic.

---

## Active project risks

These are risks to the proof architecture or optimization experiment itself.

They should influence implementation choices from the beginning.

### R1. Proofs may become coupled to exact bytecode

The optimization experiment depends on being able to change low-level RV code without rebuilding unrelated higher-level XMSS proofs.

A proof architecture that records long sequences of intermediate machine states, absolute instruction addresses, particular register allocations, or incidental implementation details will make automated optimization impractical.

**Mitigation:** expose stable semantic contracts at meaningful program boundaries.

Machine-level proofs establish these contracts. Higher-level proofs consume the contracts rather than reopening the underlying instruction sequence.

Prefer reusable local simplification lemmas, `simp`, `grind`, WP/decompilation rules, and frame lemmas over brittle instruction-by-instruction scripts.

**Early validation:** during M3, deliberately create a second implementation of `recoverChain` with a different instruction sequence and prove it against the same contract.

The proof of code calling `recoverChain` should require no substantive change.

If it does, fix the abstraction boundary before proceeding to M4.

### R2. The optimization metric may be underspecified

"Cycle count" is not meaningful until the virtual cost model and measured execution path are fixed.

The benchmark is intentionally synthetic. It is not intended to estimate SP1 proving cost, ZisK proving cost, real CPU latency, or hardware accelerator performance.

Before optimization begins, specify:

- the cost of each ordinary RV instruction;
- the cost of an abstract hash call;
- whether branches have any special cost;
- whether termination has a cost;
- whether memory operations differ from arithmetic operations;
- which inputs or execution paths determine the reported score.

A simple initial model such as:

```text
ordinary executed RV instruction = 1 cycle
abstract hash call               = configurable constant
```

is acceptable if documented explicitly.

The hash cost should ideally be controlled by one parameter so sensitivity to different assumed hash costs can be tested later.

**Agent rule:** never report a program as simply "N cycles" unless the benchmark inputs/path and cost model make that number well-defined.

### R3. Input-dependent execution can make one cycle count misleading

Verification and rejection may follow different execution paths.

Therefore the performance objective must specify what is being optimized.

Possible metrics include:

```text
cost on valid verification
worst-case cost over permitted inputs
maximum rejection cost
a fixed benchmark corpus
```

For the initial challenge, prefer a metric that is deterministic and difficult for an optimizer to game.

If valid verification has effectively fixed work because of the XMSS target-sum construction, document and prove the relevant fact rather than assuming it. M8.a must also establish the auth-path formula `auth_steps(ep) = C + 3 * popcount(ep)` so that `valid-epmax` (`ep = 2^32 - 1`) is justified as the maximum-cost accepting XMSS run, not merely observed on the current fixtures.

**Agent rule:** settle the benchmark path semantics before M9. Do not compare candidate programs using accidentally different execution paths. M8.a freezes this: primary `OTS_steps` on an accepting path; secondary `XMSS_steps` on `valid-epmax`; `hashes_OTS = 101` and `hashes_XMSS = 133` exactly; `idxAuth` is the OTS stopping point.

### R4. The abstract hash boundary extends the execution model

Hashing is deliberately abstract, but an abstract hash call is not an ordinary RV64 instruction.

The proof must distinguish clearly between:

1. execution justified by ordinary RV64 semantics;
2. the assumed semantic contract for the hash oracle.

For example:

```text
RV instructions
      |
      | ordinary machine semantics
      v
hash-call boundary
      |
      | assumed HashContract H
      v
H(input)
```

The correctness theorem should remain parametric in `H`.

The hash abstraction must specify at least:

- how input bytes are identified;
- where the result is written or returned;
- the result length;
- registers that may change;
- memory that may change;
- behavior on return;
- benchmark cost.

**Agent rule:** do not silently encode backend behavior, BLAKE2s behavior, or other concrete hash semantics into this contract. Keep it minimal and host-neutral.

### R5. The machine/spec representation boundary may grow unnecessarily

The authoritative Lean verifier is already `XmssSecurity.Concrete.verify`.

The project should not create a second independent Lean implementation of XMSS.

The machine proof only needs a precise relation between structured specification inputs and RV machine memory.

Prefer a theorem shaped approximately like:

```text
memory encodes (pk, ep, msg, sig)
              |
              v
         RV verifier
              |
              v
result = Concrete.verify pk ep msg sig
```

rather than introducing serialization and decoding into the verifier unless byte-level parsing is intentionally made part of the challenge.

A memory representation may use aligned fields and fixed offsets chosen for efficient RV execution.

**Agent rule:** keep representation predicates small and declarative. Do not introduce SSZ, frontend parsing, or a second verifier wrapper unless the project explicitly decides that serialization itself should be optimized and proved.

### R6. Optimized candidates may fail to terminate

Functional correctness must not mean only:

> if the program terminates, its answer is correct.

An automated optimizer may accidentally introduce loops or paths that fail to terminate.

The final correctness contract must include termination for every machine state satisfying the verifier precondition.

Where practical, internal region contracts should also expose bounded execution properties, especially for fixed loops such as:

- at most 7 WOTS chain iterations;
- 42 chains;
- 32 authentication levels.

**Agent rule:** an optimization candidate that preserves partial correctness but loses termination is incorrect and must fail the proof gate.

### R7. The proved program and measured program may diverge

The optimization experiment is invalid if Lean proves one artifact while the benchmark evaluates another.

There should be one canonical representation of the candidate program from which both proof and evaluation derive.

Prefer a flow like:

```text
             canonical Program
                /        \
               /          \
              v            v
         Lean proof    evaluator
              |            |
              v            v
          correct?       cycles
```

Avoid manually maintaining equivalent instruction sequences in separate proof and benchmark files.

**Acceptance requirement for M8:** demonstrate mechanically that the evaluator consumes the same program value or canonical byte representation used by the correctness theorem.

### R8. The optimizer may exploit the benchmark rather than improve the verifier

Once optimization is automated, assume the search process will exploit any mismatch between the correctness theorem and performance measurement.

Examples include:

- specializing behavior to the benchmark inputs;
- reaching an unmeasured execution path;
- exploiting undefined or underspecified machine state;
- relying on registers or memory that the theorem did not constrain;
- exploiting a discrepancy between the abstract hash semantics used by the proof and benchmark;
- reducing measured cost by violating an intended property that was never included in the theorem.

**Mitigation:** treat the theorem precondition, machine semantics, hash contract, and benchmark definition together as the specification of the optimization challenge.

Keep preconditions as strong as necessary for meaningful execution but no stronger than justified.

Make observable behavior and frame conditions explicit.

Before M9, perform an adversarial review of the theorem and benchmark specifically asking:

> What incorrect or unintended program could still pass both gates?

### R9. Optimization-resilient abstractions may themselves hide performance

Semantic contracts are necessary for proof modularity, but they must not prevent the benchmark from observing the actual instructions executed inside a region.

The proof may reason abstractly about `recoverChain`; the evaluator must still execute and count the concrete RV implementation of `recoverChain`.

**Agent rule:** abstraction is for proofs, not execution. Do not replace optimized regions with uninterpreted semantic operations in the benchmark, except for the explicitly designated hash oracle.

### R10. Proof automation can become slow or unpredictable

Heavy use of `simp` and `grind` is useful only if the supporting lemma sets remain controlled.

Large global simp sets or overly broad automation can make proof checking slow, fragile, or sensitive to unrelated imports.

That would be especially harmful once Lean becomes the inner correctness loop for automated optimization.

**Mitigation:**

- prefer local or namespaced simp sets;
- keep normalization lemmas directional;
- avoid adding expensive global `[simp]` lemmas without evidence;
- keep region proofs small;
- measure proof-check time as the implementation grows;
- factor recurring machine reasoning into targeted reusable lemmas.

**Agent rule:** proof-check latency is part of the engineering requirements for M9. If a proof is correct but takes long enough to make automated search impractical, treat that as an architectural problem rather than waiting until the final milestone.

---

## Risk checkpoints

Do not wait until M7 or M9 to discover whether the architecture supports optimization.

Use the following checkpoints:

| milestone | architectural check |
|---|---|
| **M1** | machine/spec memory relation and `HashContract H` are explicit and minimal |
| **M3** | two different `recoverChain` implementations can satisfy the same semantic contract without changing caller proofs |
| **M5** | bit-level automation remains local and proof-check time is suitable for iteration |
| **M7** | end-to-end theorem includes equivalence, termination, and frame behavior without depending unnecessarily on exact instruction layout |
| **M8.a** | exactly one `Program` on main; cost function, hash pin, and the semantic OTS cut frozen; `auth_steps` formula established; accept script checks statement integrity, the hash pin, OTS constancy, and a proof-time budget, and measures the proved `Program` |
| **M8.b** | a land is a new record (`(OTS, XMSS_epmax) < baseline`) without weakening `VerifierCorrect` |
| **M9** | `chainWalk` search with proof repair always allowed; frozen invariants; two-tier loop; passing the accept gate without a record is not an improvement |

---

## Evaluation criteria

Correctness should be evaluated independently at three levels:

1. the Lean proof itself;
2. end-to-end executable behavior;
3. executable behavior of individual verifier components.

Passing `lake build` alone is not sufficient.

The goal is to have independent checks that exercise both the formal theorem and the concrete RV execution.

### E1. Kernel-level correctness

The final implementation must be accepted by Lean with the repository's intended trust assumptions.

The basic correctness gate is:

```bash
lake build
scripts/check-axioms.sh
scripts/check-forbidden-tactics.sh
```

For the completed verifier:

- the final correctness theorem contains no `sorry`;
- declarations under `XmssAsm` use only the permitted axioms reported by the axiom gate;
- forbidden proof shortcuts such as `native_decide` and `bv_decide` do not occur;
- the theorem is about the actual RV program being implemented;
- the theorem relates its result directly to `XmssSecurity.Concrete.verify`;
- the theorem remains parametric in the abstract hash oracle `H`;
- execution is proved to terminate for every state satisfying the verifier precondition;
- the theorem states the relevant register and memory frame behavior.

The intended top-level result should have the semantic shape:

```text
memory represents (pk, ep, msg, sig)
              |
              v
        execute RV verifier
              |
              v
           terminates
              |
              v
result = Concrete.verify pk ep msg sig
```

The exact Lean statement will depend on the machine/program-logic interfaces, but weakening this result should be treated as a design change requiring explicit review.

**Acceptance criterion:** all three repository gates pass and the final theorem establishes equivalence, termination, and the intended frame properties without additional trust assumptions.

### E2. End-to-end differential execution

In addition to proving the theorem, the RV verifier should be executable under the RV interpreter and compared directly against the existing Lean specification.

For testing, instantiate the abstract hash oracle with a deterministic executable function `H_test`.

`H_test` does not need to be cryptographically secure. Its purpose is to make both sides executable while exercising the same oracle interface.

For each test case, evaluate:

```text
             (pk, ep, msg, sig)
                /          \
               /            \
              v              v
     Concrete.verify      RV verifier
         with H_test       with H_test
              |              |
              v              v
           expected         actual
               \             /
                \           /
                 v         v
                  must agree
```

The same `H_test` and logically identical structured inputs must be used on both sides.

The test harness must use the same representation function or predicate used by the theorem to initialize RV memory from the structured inputs.

The test corpus should include at least:

- valid accepting verifier inputs;
- valid rejecting inputs;
- modified signatures;
- modified public keys;
- modified authentication paths;
- boundary epoch values;
- zero-heavy and other simple edge-case values;
- deterministic pseudo-random structured inputs.

Tests should be reproducible.

Randomized tests must therefore use a fixed seed or record their generated fixtures.

The differential test harness is not part of the trusted correctness argument.

It is an independent engineering check intended to catch errors in theorem wiring, representation predicates, execution setup, and assumptions about the machine interface.

**Acceptance criterion:** every end-to-end fixture produces exactly the same boolean from `Concrete.verify` and interpreted RV execution.

The repository should expose this through one documented command, for example:

```bash
scripts/test-differential.sh
```

The exact script name is flexible, but running the complete differential suite should require no manual setup or interpretation of results.

### E3. Component-level differential tests

Important RV regions should also be tested independently against the corresponding Lean specification operation.

This provides localization when the end-to-end verifier disagrees with the specification and gives each implementation milestone an executable acceptance test in addition to its proof.

At minimum, test the major semantic boundaries introduced by the proof architecture:

```text
RV implementation              Lean reference
-------------------------------------------------------------
recoverChain               <-> recoverChain
recoverEndpoints           <-> corresponding scheme operation
leafHash                   <-> leafHash
decodeDigest               <-> TargetSum.decodeDigest
authenticationRoot         <-> authenticationRoot
```

For reusable one-step blocks such as `recoverChainStep`, `decodeDigit`, or `authStep`, add direct component tests where the corresponding upstream semantics can be isolated cleanly.

Each test should:

1. construct a valid machine state for the region;
2. execute the concrete RV instructions;
3. evaluate the corresponding Lean operation on the same logical inputs;
4. decode or inspect the resulting machine state;
5. assert equality with the Lean result;
6. check important frame properties where practical.

Small finite domains should be tested exhaustively when inexpensive.

In particular, `recoverChain` has only eight possible digit values:

```text
0, 1, 2, 3, 4, 5, 6, 7
```

Every one should be exercised.

Other inputs such as starting digests can use fixed edge cases plus deterministic pseudo-random values.

Tests for `decodeDigest` should deliberately exercise:

- valid target-sum encodings;
- incorrect target sums;
- padding-bit failures;
- boundary digit values;
- simple bit patterns;
- deterministic pseudo-random digests.

Authentication-path tests should exercise both left/right child orderings and epoch-bit boundaries.

Component tests should be added alongside the implementation rather than postponed until the full verifier exists.

**Milestone requirement:**

| milestone | executable evaluation |
|---|---|
| **M2** | hash-interface and tweak/payload construction tests |
| **M3** | `recoverChainStep` / `recoverChain` differential tests, including all digit values `0..7` |
| **M4** | endpoint recovery and leaf-construction differential tests |
| **M5** | `decodeDigit` / `TargetSum.decodeDigest` differential and boundary tests |
| **M6** | `authStep` / authentication-path differential tests covering both branch orderings |
| **M7** | complete end-to-end differential suite |

**Acceptance criterion:** each implemented semantic region agrees with its corresponding Lean operation on its complete deterministic test suite, and the relevant component suite is required to pass before its milestone is considered complete.

### Evaluation philosophy

The three evaluation layers serve different purposes:

```text
Lean kernel proof
    proves the stated theorem for all inputs
             |
             v
end-to-end differential tests
    check that theorem, machine setup, and spec are wired together correctly
             |
             v
component differential tests
    independently exercise and localize the concrete implementation
```

The Lean theorem is the actual correctness argument.

Differential testing does not replace it.

Conversely, the existence of a proof should not be used as a reason to omit executable tests.

The tests provide an independent check that the project has proved and executed the artifact it intended to build.

---

## Milestones

Each implementation milestone is complete only when its code, proof, executable tests, and cycle measurement are complete.

A region that merely compiles or has a partial proof is not considered finished.

The milestones are deliberately ordered so that the risky architectural assumptions are tested early.

By the end of M3, the project should have demonstrated the complete workflow on a small but real part of the verifier:

- write RV code;
- execute it;
- call the abstract hash oracle;
- prove it against the Lean specification;
- test it differentially;
- measure it;
- replace it with another implementation;
- preserve its semantic contract.

### M0. Repository scaffold

Establish a working repository in which the XMSS specification and RV machine infrastructure are available on the same Lean toolchain.

**Acceptance criteria:**

```bash
lake build
scripts/check-axioms.sh
scripts/check-forbidden-tactics.sh
```

All pass.

`XmssSecurity.Concrete.verify` and the required RV execution/program-logic definitions are reachable from the project.

**Status:** complete.

---

### M1. Machine/specification contract

State the exact boundary between the existing Lean XMSS specification and the RV implementation before writing substantial verifier code.

Define:

- the RV program entry convention;
- the representation of `PublicKey`, `Epoch`, `Message`, and `Signature` in machine memory;
- the precondition relating machine memory to those structured Lean values;
- the boolean result convention;
- permitted scratch memory;
- relevant register and memory frame behavior;
- the abstract `HashContract H`;
- the termination condition;
- the top-level `xmss_verify_correct` theorem statement.

The authoritative verifier specification remains `XmssSecurity.Concrete.verify`.

No `verifyBytes` or second verifier wrapper should be introduced.

The intended theorem should have approximately this semantic shape:

```text
memory represents (pk, ep, msg, sig)
              |
              v
        execute RV verifier
              |
              v
           terminates
              |
              v
result = Concrete.verify pk ep msg sig
```

The theorem may contain `sorry` at this milestone.

Its interface should be treated as stable once M2 begins.

Add a tiny executable RV/spec smoke test that demonstrates that the chosen machine representation and execution machinery can be exercised from the repository.

**Acceptance criteria:**

- `xmss_verify_correct` has been stated;
- the machine/spec memory relation is explicit;
- `HashContract H` is explicit and host-neutral;
- result, termination, and frame behavior are explicit;
- no SP1/ZisK/backend assumptions appear in the contract;
- the basic executable smoke test passes;
- the theorem statement has received an adversarial review for accidentally over-strong preconditions or under-specified outputs.

---

### M2. Execution, hash, and measurement infrastructure

Build the infrastructure that every subsequent verified region will use.

Implement the abstract hash-call mechanism and prove the basic contract connecting it to `H`.

Establish reusable `hashCall` and `tweakableHashStep` blocks, or equivalent semantic contracts, that later regions can compose.

Implement and test the low-level byte operations needed to construct XMSS hash tweaks and payloads, including the required `HashDomain` cases.

Establish a deterministic RV evaluator and cycle counter.

The same canonical `Program` representation must feed:

```text
             canonical Program
                /        \
               /          \
              v            v
         Lean proof    evaluator
                           |
                           v
                       cycle count
```

The initial cost model should be simple and explicit.

For example:

```text
ordinary executed RV instruction = 1 cycle
abstract hash call               = hashCost
```

where `hashCost` is one configurable parameter.

**Acceptance criteria:**

- abstract hash calls execute under the evaluator;
- their semantic contract is proved;
- reusable hash/tweak blocks are established;
- tweak and payload construction has component-level tests;
- the evaluator deterministically reports executed instruction count, hash-call count, and total synthetic cost;
- the cost model is documented;
- proof and evaluator consume the same canonical program artifact;
- all E1 and applicable E3 evaluation gates pass.

---

### M3. `recoverChain` and proof-architecture validation

Implement and prove one complete WOTS chain walk.

For digit `x`, the region must perform exactly the semantic operation represented by the upstream `recoverChain`, including the remaining:

```text
7 - x
```

hash steps.

First isolate the repeated chain-step operation, `recoverChainStep` or equivalent.

Implement it as a reusable RV block and prove its semantic contract.

Then prove the full chain as a bounded repetition or composition of that step, matching the upstream semantics.

This milestone is also the deliberate stress test for optimization-resilient proofs.

Implement two meaningfully different RV instruction sequences for `recoverChain` and prove both against the same semantic contract.

For example:

```text
implementation A ----\
                      \
                       >---- recoverChain contract
                      /
implementation B ----/
```

Any caller of that contract should remain unchanged apart from selecting which implementation satisfies it.

Differential tests must exercise every possible chain digit:

```text
0 1 2 3 4 5 6 7
```

using edge-case and deterministic pseudo-random starting digests under the same executable test oracle.

Record the cycle cost of both implementations.

**Acceptance criteria:**

- `recoverChainStep` or its equivalent reusable block is proved;
- `recoverChain` is proved as bounded composition of chain steps;
- all digits `0..7` are differentially tested;
- two different implementations satisfy the same `recoverChain` semantic contract;
- changing between those implementations does not require substantive changes to caller-level proofs;
- termination/frame behavior is proved;
- cycle counts are reported for both implementations;
- all E1 and applicable E3 gates pass.

**Stop condition:** if changing the implementation causes higher-level semantic reasoning to break, fix the proof boundary before beginning M4.

---

### M4. WOTS endpoint recovery and leaf construction

Use the M3 `recoverChain` contract to recover all 42 WOTS chain endpoints.

The 42-chain proof should compose the already-proved `recoverChain` contract 42 times.

It should not duplicate the chain machine reasoning or reopen the concrete chain-walk instruction sequence.

Then implement the leaf construction corresponding to the upstream specification.

**Acceptance criteria:**

- `recoverEndpoints` is proved as a composition of 42 `recoverChain` contracts;
- leaf construction is proved against the corresponding Lean specification;
- component-level differential tests pass;
- the proof does not depend unnecessarily on the concrete implementation selected for `recoverChain`;
- termination and relevant frame properties are proved;
- cycle measurements are recorded;
- all E1 and applicable E3 gates pass.

---

### M5. Target-sum digest decoding

Implement and prove the RV equivalent of `TargetSum.decodeDigest`.

Isolate a reusable digit-extraction block, `decodeDigit` or equivalent, and use it to structure the proof for decoding all 42 digits where practical.

This includes:

- extracting all 42 three-bit digits;
- enforcing the required padding-bit conditions;
- checking or deriving the target sum of 195;
- handling rejection exactly as required by the specification.

This milestone is expected to contain substantial bit-level reasoning and should be used to validate that the chosen `simp` / `grind` infrastructure remains fast and local.

Differential tests should include:

- valid target-sum digests;
- invalid target sums;
- padding-bit failures;
- boundary digit values;
- simple bit patterns;
- deterministic pseudo-random digests.

**Acceptance criteria:**

- the reusable digit-extraction operation is proved;
- the RV region is proved equivalent to `TargetSum.decodeDigest`;
- boundary and differential tests pass;
- rejection behavior agrees with the specification;
- proof automation remains suitable for repeated development;
- cycle measurement is recorded;
- all E1 and applicable E3 gates pass.

---

### M6. Merkle authentication path

Implement and prove the 32-level authentication-path computation corresponding to `authenticationRoot`.

The verifier reconstructs a root from the supplied authentication path.

It does not construct or store an explicit Merkle tree.

For each authentication level, implement a reusable operation, `authStep` or equivalent, with its own stable contract.

That operation should perform the semantic equivalent of:

1. inspect the relevant epoch bit;
2. select the correct left/right child ordering;
3. construct the required hash input;
4. invoke the abstract hash;
5. produce the parent node.

Then prove `authenticationRoot` as bounded composition of 32 `authStep` contracts.

Tests must exercise both left/right orderings and relevant epoch-bit boundaries.

**Acceptance criteria:**

- `authStep` or its equivalent reusable operation is proved;
- the 32-level computation is proved as composition of 32 authentication steps against the Lean specification;
- both child orderings are differentially tested;
- epoch-bit boundary cases are tested;
- termination and frame behavior are proved;
- the caller depends on the semantic contract rather than the internal instruction sequence;
- cycle measurement is recorded;
- all E1 and applicable E3 gates pass.

---

### M7. End-to-end verifier

Compose the verified regions into the complete RV XMSS verifier.

Conceptually:

```text
machine representation
        |
        v
target-sum decoding
        |
        v
42 WOTS chain recoveries
        |
        v
leaf construction
        |
        v
32-level authentication path
        |
        v
root comparison
        |
        v
Bool
```

Discharge the `xmss_verify_correct` theorem stated in M1.

The final result must establish, for every machine state satisfying the input representation predicate:

```text
RV result = Concrete.verify pk ep msg sig
```

together with termination and the documented frame behavior.

The theorem remains parametric over the abstract hash oracle `H`.

Run the complete end-to-end differential suite using the same deterministic executable test oracle on both the Lean specification and RV interpreter.

**Acceptance criteria:**

- M1's `sorry` is completely discharged;
- the final theorem establishes full equivalence;
- termination is proved;
- frame behavior is proved;
- no additional trust assumptions have appeared;
- all end-to-end differential fixtures agree with `Concrete.verify`;
- the complete E1, E2, and E3 evaluation gates pass;
- the complete verifier's baseline cycle measurement is recorded.

---

### M8. Verified optimization

The M3 dual walk (`chainWalkA` / `chainWalkB`, `verifier` / `verifierB`) was a
proof-architecture checkpoint: two sequences, one contract, four declared
swap sites. It is not how main should look during optimization. M8.a
collapses that dual, freezes the metric and the optimization contract, and
installs the accept gate. M8.b is the first *new record* after that
baseline. From M8.a on, do not retain alternate candidate implementations
in-tree; `main` is the single best-known artifact and Git history is the
leaderboard.

#### M8.a Single artifact, frozen metric, accept gate

Do this before any further optimization or harness work.

**One program on main.** The artifact becomes the hoisted chain walk (today's
`chainWalkB`: 20 instructions, constants out of the loop). Delete
`chainWalkA`, `verifierB` / `verifierCodeB`, `implB` / `buildB`, and the
second named proof `chainWalkB_correct`. The surviving body is `chainWalk`;
its proof is `chainWalk_correct`. `difftest` and `lake exe cycles` run that
one code map. Git history keeps the A→B→A experiment; main does not.

This is also a cycle win relative to the M7 baseline (A): OTS 3231 → 2634
steps, XMSS `valid-epmax` 4427 → 3830, both still 101 / 133 hash calls.
Record those post-collapse numbers as the M8.a baseline. Static size 183.

**Cost function** (lexicographic; hashes are an exact pin, not a score term):

```text
primary:    OTS_steps on an accepting path
secondary:  XMSS_steps on fixture valid-epmax
constraint: hashes_OTS  = 101
            hashes_XMSS = 133
            E1 + E2 + E3 pass, xmss_verify_correct holds
```

OTS means init + decode + 42 WOTS chains + leaf, stopping at `idxAuth`.
That cut is part of the optimization contract: a candidate must not move
work past the cut merely to shrink `OTS_steps`.

The cut is **semantic, not numeric**: it is the boundary after the leaf hash
and before the first authentication instruction, however the program is
renumbered. `idxAuth` is *not* a constant -- it is
`idxLeaf + leaf.length`, so it moves whenever the chain walk's length moves,
and M9 explicitly permits changing any index that is a function of that
length. What is immutable is which work falls on each side of the boundary,
not the number that names it.

OTS `steps` is constant on every accepting fixture: target-sum 195 forces 99
remaining chain hashes, plus 1 encoding and 1 leaf. That constancy is a
property of the current program, not of every candidate -- a walk with a
digit-dependent fast path would break it and make "an accepting path"
ambiguous. The accept gate therefore **asserts** it: `OTS_steps` must agree
across all accepting fixtures, and a candidate whose OTS cost varies by
fixture fails the gate. This is why no held-out fixture corpus is needed.

XMSS on `valid-epmax` is the worst-case accepting run. M8.a must prove or
mechanically establish

```text
auth_steps(ep) = C + 3 * popcount(ep)
```

for a documented constant `C` (the all-zero-epoch auth cost). Then
`ep = 2^32 - 1` is the unique maximum-cost accepting epoch, not an
observation on the current fixtures. Do not average over random epochs.

The exact hash pin keeps the problem on RV instruction overhead. Extra
oracle queries can still satisfy `VerifierCorrect`; they fail the gate
anyway. `hashCost` stays as a reporting parameter; among candidates that
meet the pin it does not change the ranking. At `hashCost = 1`,
`cost = steps`.

**Stretch target: `OTS_steps = 512`.** Recorded here as what "really good"
would look like, not as a gate condition. The gate is `m <= baseline` and
stays that way; 512 is a marker to aim at, and a candidate that misses it is
not thereby a failure.

It is a hard target, and worth writing down why, so that work aims at the
right regions. The OTS path today is 2139 steps:

```text
  init (encoding hash)      43
  decode digits            222
  42 chain walks          1858
  leaf hash                 16
                          ----
                          2139
```

and the 1858 breaks down as 42 x 20 chain-loop overhead (load 9, store 10,
branch 1) + 42 x 10 walk prologue + 99 x 5 per-step work + 99 hash `ECALL`s
+ 4 for the loop header. So:

- the 101 hash `ECALL`s of the OTS path are 101 steps that cannot go, since
  the hash pin is an equality. That is a fifth of the target on its own;
- each chain step must write a *different* tweak word (the position
  changes), so roughly one store per step, ~99 more, is close to forced;
- that leaves ~310 steps for everything else: reading 42 chain values,
  extracting and target-sum-checking 42 digits, the leaf payload, and all
  loop control. Decode alone is 222 today.

Reaching 512 therefore needs more than the `chainWalk` search space M9 opens:
`decode` and the chain load/store overhead have to come down too, and the
per-step work has to approach the `ECALL`-plus-one-store floor. Opening those
regions is a deliberate decision, not a consequence of this target -- M9's
restriction to `chainWalk` stands until that loop has been run and reviewed,
and the stopping points and hash pin stay frozen either way.

Do **not** put in the score: reject-path cost, static instruction count,
wall time, proof-check latency, or ots.golf compressions (this evaluator
charges one unit per hash `ECALL` regardless of input length). Reject
fixtures remain a termination / fuel filter. Size is a tie-break at most.
Proof-check time is recorded for every gate-passing candidate as an
engineering constraint on autoresearch throughput (R10), not as part of
the verifier performance objective.

**Gate vs record.** Distinguish a candidate that passes without regressing
from a candidate that is a new record. Let
`m = (OTS_steps, XMSS_epmax_steps)` in lexicographic order.

```text
gate pass:   proofs + tests + hashes_OTS = 101 + hashes_XMSS = 133
             and  m ≤ baseline
new record:  gate pass and  m < baseline
```

Only a new record updates the committed baseline and may be called an
improvement. A gate pass with `m = baseline` is allowed (refactor, proof
cleanup) and does not change the record. A candidate with `m > baseline`
fails the gate, even if the theorem holds.

**Accept gate.** One script (`scripts/accept.sh` or equivalent):

1. **statement integrity.** Check that the `VerifierCorrect` and
   `Represents` definitions are byte-identical to their pinned form. A
   weakened statement -- an added hypothesis, a dropped conjunct -- builds
   cleanly, passes the axiom sweep, passes every fixture, and scores
   better. Nothing else in this list catches it, so it is checked first;
2. `lake build` (`xmss_verify_correct` typechecks), under a **wall-clock
   budget**; exceeding the budget is a reject, not a slow pass. Proof-check
   time is excluded from the score but bounded as a gate condition, because
   a single candidate must not be able to stall the loop (R10);
3. `scripts/check-axioms.sh` and `scripts/check-forbidden-tactics.sh`;
4. `scripts/test-differential.sh` (the one program);
5. assert the hash pin (`hashes_OTS = 101`, `hashes_XMSS = 133`) and assert
   that `OTS_steps` is equal across all accepting fixtures;
6. dump `OTS_steps`, `XMSS_epmax_steps`, hash counts, and proof-check
   time against a **machine-readable baseline** committed in-tree;
7. exit non-zero on statement, proof, timeout, test, hash-pin,
   OTS-constancy, or `m > baseline` failure; exit 0 on gate pass; update
   the baseline file only on a new record.

The theorem and the evaluator consume the same `Program` value (R7).
`lake exe cycles` is the region-split report (OTS vs Merkle); tighten it to
the single program and, if the accept script needs it, a parseable dump.
`main` is the single best-known artifact. Git is the leaderboard.

There is no theorem that a given `Program` is *optimal*. The loop is
best-so-far. A lower bound (ots.golf-style) is a different project.

**Frozen before M9** (the optimization contract; a candidate that changes
any of these is out of spec, not an optimization):

- the same canonical `Program` is both proved and measured;
- the `VerifierCorrect` theorem statement cannot change;
- the machine / input representation cannot change;
- the hash-oracle semantics cannot change;
- benchmark inputs and stopping points cannot change (`idxAuth` for OTS;
  full run on `valid-epmax` for XMSS);
- hash counts remain pinned at 101 / 133;
- only a strict metric improvement (`m < baseline`) updates the committed
  baseline;
- the **scoreboard and the gate itself are not candidate material**: the
  committed baseline file, `scripts/accept.sh`, `scripts/check-axioms.sh`,
  `scripts/check-forbidden-tactics.sh`, `scripts/test-differential.sh` and
  the fixture corpus are off limits to a candidate. Editing a number in the
  baseline file is cheaper than weakening a proof, and step 6 writes to
  that file; a denylist that protects the theorem but not the scoreboard is
  exactly the mismatch R8 warns about. Only a human, in a separate commit,
  changes the gate or the corpus.

When whole-program optimization is later enabled, region boundaries and
those stopping points stay immutable unless the metric is redesigned.

**Correctness of a land.** Every candidate that lands on `main` must
re-establish the *unchanged* `xmss_verify_correct` / `VerifierCorrect`
theorem for the *exact* `Program` the evaluator measures. A green
differential suite is never a substitute for that proof.

**Proof repair is always permitted** in M8 and M9. A candidate may edit
local proofs of the affected region so that they close again. Validity
still requires that those proofs re-establish the *same* local contracts
(`ChainWalkPre` / `ChainWalkPost`, and so on) *and* the unchanged
top-level `xmss_verify_correct`. Weakening a contract, changing the
theorem statement, or landing with `sorry` is out of spec.

Proof robustness is an **iteration goal**, not a restriction on the
search and not a soundness assumption. Tactful `simp` / `grind`, local
contracts, and region insulation should make most `chainWalk` edits cheap
to re-close — ideally no repair above the affected region (`chainWalk_correct`
re-closes; `chains_correct` and `Verify.lean` stay untouched). If a change
forces broader proof edits, the architecture missed that goal; the
candidate can still land once the repaired proofs meet the bar above.

**Acceptance criteria:**

- exactly one RV implementation of the verifier on main; no in-tree
  alternate candidates;
- `chainWalk_correct` is the only chain-walk correctness theorem in the
  artifact; callers still go through that contract;
- cost function, gate-vs-record rule, hash pin, and stopping points are
  documented here and in `docs/CONTRACT.md`;
- `auth_steps(ep) = C + 3 * popcount(ep)` is proved or mechanically
  established, so `valid-epmax` is justified as worst-case accepting XMSS;
- a machine-readable baseline is committed (OTS 2634 / 101 hashes; XMSS
  epmax 3830 / 133 hashes, after the collapse);
- one accept command implements gate pass (`m ≤ baseline`) vs new record
  (`m < baseline`), with hashes exact, statement integrity checked
  mechanically, `OTS_steps` asserted equal across accepting fixtures, and a
  proof-check wall-clock budget enforced;
- the baseline file, gate scripts, and fixture corpus are documented as
  off limits to candidates;
- a land re-establishes unchanged `xmss_verify_correct` for the measured
  `Program`; differential tests are not a substitute;
- dual A/B builds, dual cycle reports, and `verifierB` are gone;
- `lake build` is warning-free; E1/E2/E3 pass on the single program.

**Stop condition:** if tests or the evaluator still take a `Build` / `code`
parameter that can silently measure a different `Program` than
`xmss_verify_correct`, fix that before M8.b.

#### M8.b Overwrite the artifact

From the M8.a baseline, optimize the single program. A candidate is a
**patch to that program** (start with `chainWalk`; later regions only when
explicitly opened), never a second `implC` living next to it.

```text
candidate patch
       |
       +---- proof/tests/hash pin ---- fail ----> reject
       |
       +---- gate: m ≤ baseline
                     |
                     +---- m = baseline ----> gate pass, not a record
                     |                        (do not update baseline)
                     |
                     +---- m < baseline ----> new record:
                                              overwrite main, update baseline
```

Track at least (report; only the frozen pair is the score):

- static instruction count;
- executed ordinary RV instructions;
- abstract hash calls (must be 101 / 133);
- total synthetic cost at the documented `hashCost`;
- proof-check time (recorded, not scored).

A new record *overwrites* the previous implementation. The previous record
is the last commit and the old baseline line, not a retained alternate
`Program`.

**Instructive rejects are kept, as fixtures rather than as programs.** The
no-alternates rule bans a live alternate `Program` that a caller could
select; it does not ban recording what went wrong. A candidate that failed
for a reason worth remembering -- lost termination, broke the hash pin,
regressed the metric in a non-obvious way, needed proof repair above its
region -- is recorded in `XmssAsmTests/Rejects.lean` as an instruction list
plus the expected failure, and the suite asserts it still fails for that
reason. Those lists are test data: nothing outside the reject suite may
refer to them, and they are never reachable from `verifier`.

The four swap sites (`chainWalk`, `chainWalk_length`, `bOff_chainsLoop`,
`chainWalk_correct`) are the interface. Proof repair of the walk (and, if
needed, its local proof file) is always allowed. Robustness — re-closing
with existing automation, no edits above the region — is the iteration
goal (`simp` / `grind`, stable contracts). Soundness does not assume it
succeeded. After any repair, the land is valid only if the same local
contracts and the unchanged `xmss_verify_correct` hold for the measured
program. A candidate may not weaken `VerifierCorrect`, the hash pin, the
stopping points, or the cost-function paths. Differential tests do not
replace that theorem.

The M8.a collapse (A → hoisted walk) does **not** close M8.b. M8.b requires
at least one further candidate attempted against that baseline. Landing a
new record is optional; attempting it is not.

**Acceptance criteria:**

- at least one nontrivial candidate is attempted from the M8.a baseline;
- any overwrite of main is a new record (`m < baseline`), re-establishes
  unchanged `xmss_verify_correct` for the measured `Program`, and passes
  E1, E2, E3 with hashes exact; tests are not a substitute for the proof;
- performance comparisons use the M8.a paths (accepting OTS; XMSS on
  `valid-epmax`), never a lucky random epoch;
- higher-level proofs remain insulated from the local instruction sequence
  where M3 intended (iteration goal; repair above the region is allowed
  but is a robustness miss);
- benchmark results are reproducible from the committed `Program` and
  baseline file;
- proof-check time is recorded for every gate-passing candidate.

---

### M9. Autoresearch harness

Package the M8.a accept gate so an untrusted agent can propose a patch and
get a yes/no plus numbers. The optimizer is not trusted. Correctness is
the same theorem and gates as manual work. The M8.a frozen invariants
remain in force.

**Search space (first version): `chainWalk` only**, plus whatever local
proof repair that body needs. The untrusted optimizer may modify:

- the designated RV implementation region (`chainWalk` / `chainStep`);
- mechanically necessary offsets / lengths (`chainWalk_length`,
  `bOff_chainsLoop`, and any index that is a function of that length);
- local proofs of that region (`XmssAsm/Regions/Chain.lean`, and the
  `chainWalk_correct` selector).

It may **not** modify theorem *statements* (`VerifierCorrect`,
`xmss_verify_correct`), specification code, representation predicates,
hash semantics, or benchmark definitions. It may **not** touch the
scoreboard or the gate: the committed baseline file, `scripts/accept.sh`,
the two trust-gate scripts, `scripts/test-differential.sh`, or the fixture
corpus. Lowering a baseline number is the cheapest cheat available and is
easier than weakening a proof, so the boundary is enforced mechanically
(the accept script rejects a candidate diff that touches any denied path)
rather than assumed. Restricting the *code* search
to `chainWalk` keeps failures local and interpretable and avoids
conflating optimizer quality with whole-program proof-architecture
issues. Do not open other regions, and do not enable whole-program
search, until this `chainWalk` loop has been run and reviewed.

Proof repair is part of the loop, not a later mode. The Lean kernel is
the trust boundary: after repair, the same local contracts and the
unchanged top-level theorem must close. Prefer that existing `simp` /
`grind` and region insulation re-close with no edit above
`chainWalk_correct`; that is infrastructure quality, not a harness ban
on touching proofs.

Two tiers (keep this split):

*Inner loop (search).* Untrusted cheap filters on `chainWalk` mutations:
digit `0..7` chain tests, `OTS_steps` on one accepting fixture, hash pin.
Reject obvious losers. This loop must not land on main by itself.

*Land on main.* `scripts/accept.sh`. The land must re-establish the
unchanged `xmss_verify_correct` for the exact `Program` being measured.
If `chainWalk_correct` / `xmss_verify_correct` does not close, the
candidate does not merge, even when `difftest` is green. Differential
tests are never a substitute for the formal proof and are not the merge
gate. A land that is a new record updates the baseline; a gate pass that
is not a record does not.

```text
propose patch to chainWalk (+ mechanical offsets/lengths
       + local proof repair, always allowed)
       |
       v
  (optional) inner-loop filters
       |
       v
  scripts/accept.sh          (E1, E2, E3, metric dump, hash pin)
       |
       +---- fail -----------------> reject
       |
       v
  m ≤ baseline                 (gate pass)
       |
       +---- m = baseline --------> not a record; do not update baseline
       |
       +---- m < baseline --------> new record:
                                    overwrite main, update baseline,
                                    record Program + metrics
                                    + proof-check time
```

Because the first search rewrites only `chainWalk`, OTS and XMSS move by
the same Δ; XMSS is then a sanity check, not a second objective. Do not
treat that as a reason to drop the lex pair: the frozen metric stays in
place for later whole-program work, where an OTS-only cut is gameable by
pushing work past `idxAuth`. Whole-program search, if enabled, still
cannot move those stopping points.

The harness records enough to reproduce every *new record*: the `Program`
literal (or the commit that is that literal), the metric dump, proof-check
time, and which baseline it beat. `main` remains the single best-known
artifact. Git is the leaderboard. Do not keep losing or tied candidates
in-tree **as programs** -- but do record instructive rejects as fixtures in
`XmssAsmTests/Rejects.lean` (see M8.b), which is test data and not a
selectable implementation.

Every candidate runs under a wall-clock budget for the proof check, and
exceeding it is a reject. Proof-check time stays out of the score and in
the record; the budget exists so one pathological candidate cannot stall
the search. This codebase is sensitive to it: one authentication-path proof
went from a hard timeout to nine seconds purely by changing when values
were rewritten into the symbolic state.

**Acceptance criteria:**

- one documented command evaluates a candidate end-to-end;
- incorrect candidates cannot reach performance-acceptance;
- every land re-establishes unchanged `xmss_verify_correct` for the
  measured `Program`; differential tests are never a substitute;
- proof, tests, and evaluator operate on the same candidate `Program`;
- the mutation boundary is enforced mechanically, by rejecting a candidate
  diff that touches a denied path: `chainWalk` plus mechanical
  offsets/lengths plus local proof repair are allowed; theorem statements,
  spec, representation, hash semantics, benchmark definitions, the baseline
  file, the gate scripts and the fixture corpus are not;
- statement integrity is checked mechanically on every land, not assumed;
- a proof-check wall-clock budget is enforced, and exceeding it rejects;
- instructive rejects are recorded as fixtures, not as selectable
  programs;
- proof repair is always allowed; robustness (`simp` / `grind`, region
  insulation) is the iteration goal, not a code-only restriction;
- accepted new records and measurements are reproducible, including
  recorded proof-check time;
- the baseline file updates only on `m < baseline`; `main` has one
  implementation;
- proof-check and evaluation latency are practical enough for repeated
  search (R10), as an engineering constraint, not a score term.

---

## Milestone summary

| milestone | result |
|---|---|
| **M0** | repository and trust gates work |
| **M1** | machine/spec theorem boundary is fixed |
| **M2** | RV execution, reusable hash/tweak blocks, and cycle measurement work |
| **M3** | reusable chain step and `recoverChain` contract are proved, tested, measured, and successfully replaceable behind a stable contract |
| **M4** | composition across 42 WOTS chains plus leaf construction is verified |
| **M5** | reusable digit extraction plus target-sum decoding is verified |
| **M6** | reusable authentication step composed across 32 levels is verified |
| **M7** | complete RV verifier is proved equivalent to `Concrete.verify` |
| **M8.a** | one program on main; cost function, hash pin, and stopping points frozen; `auth_steps` formula; accept gate distinguishes pass vs new record |
| **M8.b** | a further candidate is attempted; main and the baseline update only on a strict metric record |
| **M9** | `chainWalk` search with proof repair always allowed; two-tier loop; land only through the accept gate |

---

## Expected scale

With the cryptographic hash primitive abstracted away, the verifier is algorithmically small.

The remaining RV logic consists mainly of:

- byte and word manipulation;
- bit extraction;
- fixed-bound loops;
- index and address arithmetic;
- hash-call setup;
- memory loads and stores;
- comparisons and branching.

The major repeated structures are statically bounded:

- 42 WOTS chains;
- at most 7 remaining steps in one chain;
- 32 authentication levels;
- 42 digest digits.

The resulting **static program** is expected to be relatively small, plausibly on the order of hundreds of RV instructions.

This is only a rough expectation and is not a design constraint.

The **dynamic executed instruction count** will be substantially larger because the loop bodies execute repeatedly during verification.

Do not optimize toward a predicted code size.

Record the first straightforward proved implementation as the empirical baseline, then measure improvements from that baseline.

At minimum, report:

- static instruction count;
- dynamically executed ordinary RV instructions;
- abstract hash-call count;
- total synthetic cycle cost.

---

## Non-goals

The following are explicitly outside the initial project:

- proving BLAKE2s;
- implementing BLAKE2s in RV64;
- SP1 integration;
- ZisK integration;
- zkVM proving-cost optimization;
- host I/O syscalls;
- frontend protocols;
- SSZ compatibility;
- reproducing leanVM's production serialization;
- introducing a second Lean implementation of the XMSS verifier;
- re-proving the upstream XMSS security theorem;
- trusting the optimizer.

These can be layered on later without changing the core verifier theorem if the abstraction boundaries are chosen well.

---

## Done

- 2026-09-15: **M0** scaffold builds warning-free; both gates pass; `XmssSecurity.Scheme` elaborates on Lean v4.33.0 / VCVio `3ecd5523`; dependencies pinned on one toolchain.
- 2026-09-17: project direction clarified: pure virtual RV64, abstract hash oracle, direct memory-to-spec representation relation, proof-preserving optimization, deterministic cycle benchmark, reusable verified blocks, and no zkVM backend in the core project.
- 2026-09-17: **M1** contract stated (`VerifierCorrect`, `docs/CONTRACT.md`): `HashContract H` as the stepper `stepH`, fixed dword layout, `Represents`, termination as `SyscallHalted`, `Frame InScratch`; theorem shape reviewed. Also landed early: the full verifier program (185 instructions), the evaluator/cycle counter, and the end-to-end differential harness (104 fixtures, all agree; accepting runs 4331-4427 steps incl. 133 hash calls).