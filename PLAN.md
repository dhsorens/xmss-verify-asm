# PLAN

The work queue and current design decisions. **Start here.** `README.md` is the repository contract; this file records what remains to be implemented and proved. Nothing here is frozen.

Dates are absolute. Today is 2026-09-17; the repository is still a scaffold.

---

## Where this is

Scaffolded, not started. The four dependencies are pinned on one toolchain
(Lean v4.33.0, Mathlib `db584cd6`), the axiom and forbidden-tactic gates are in
place, and `XmssAsm/Smoke.lean` / `XmssAsm/Spec.lean` check that the machine
side and the spec side are both reachable from one package.

No verifier code has been written and no correctness theorem has been proved.

The project target is now:

> Produce pure RV64 bytecode implementing the XMSS verifier, prove it equivalent to the existing Lean specification, measure its virtual RV cycle count, and make the proof architecture robust enough that the bytecode can be aggressively optimized without rebuilding the high-level proof.

Concrete zkVM deployment, SP1/ZisK integration, and concrete BLAKE2s verification are outside the core scope.

---

## Project objective

This is a backend-independent verified-code optimization challenge.

Given the existing Lean specification of the XMSS verifier:

1. define a byte-level reference function corresponding to the verifier;
2. implement that verifier in pure RV64 bytecode;
3. prove the RV64 implementation functionally equivalent to the Lean reference;
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

No zkVM backend, concrete hash implementation, frontend protocol, or host ABI is required for the core result.

---

## Architecture

The verifier is deliberately designed around a small set of stable boundaries. These are not pending choices. They define the shape of the project and should only be revisited if implementation experience shows that one of them is getting in the way.

### Pure virtual RV64 execution

The core artifact is a pure RV64 program running under the trusted RISC-V model.

There is no SP1 backend, no ZisK backend, and no host ABI in the main theorem or benchmark.

Inputs are already present as bytes in machine memory when execution begins. The verifier runs entirely inside the virtual RV machine and terminates with a boolean result.

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

The RV code calls a fixed host-neutral hash interface. The correctness theorem assumes a semantic contract saying that this interface returns `H(input)` and respects its documented memory and register frame. Think of it as a special risc-v instruction that has an associated cost to it (we'll start with 1 riscv cycle, though we may want to adapt that).

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

For benchmarking, an abstract hash call receives a fixed synthetic cost, which can be adjusted with a single parameter ideally.

That cost is part of the benchmark definition only. It is not intended to model real hardware, SP1, ZisK, or any other zkVM.

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

### Byte-oriented verifier interface

The external shape of the challenge is a total byte-level function:

```text
ByteArray -> Bool
```

`Concrete.verify` operates on structured Lean values such as:

```text
PublicKey
Epoch
Message
Signature
```

The Lean side should therefore expose a byte-level wrapper such as:

```lean
def verifyBytes (input : ByteArray) : Bool :=
  match decodeInput input with
  | some (pk, ep, msg, sig) =>
      Concrete.verify pk ep msg sig
  | none =>
      false
```

The RV theorem can then compare two objects with the same observable interface:

```text
RV bytes -> Bool
Lean bytes -> Bool
```

The input encoding should be:

- fixed;
- deterministic;
- cheap to decode;
- easy to prove;
- convenient for RV execution.

Compatibility with leanVM's SSZ representation is not required for the initial optimization challenge.

Internally, the implementation may use aligned fields or other convenient layouts as long as the byte-level behavior is preserved.

### Full functional equivalence

The target theorem proves full functional equivalence rather than soundness alone.

For every byte input, RV execution should terminate and return exactly the same boolean as the Lean byte-level reference function.

Conceptually:

```text
runRV verifier input = verifyBytes input
```

This includes:

- valid accepting inputs;
- valid rejecting inputs;
- malformed encodings.

The theorem should also state the relevant frame behavior so that it is explicit which memory and registers the verifier is allowed to modify.

### Optimization-resilient proof boundaries

The proof architecture is designed so local bytecode optimizations do not cascade through the entire proof tree.

Each meaningful region should expose a small stable semantic contract, for example:

```text
decodeDigest contract
recoverChain contract
recoverEndpoints contract
leafHash contract
authenticationRoot contract
verify contract
```

Machine-level proofs establish these contracts.

Higher-level XMSS proofs compose them.

For example:

```text
RV instructions for one chain walk
              |
              | machine proof
              v
      recoverChain contract
              |
              | semantic composition
              v
       42-chain proof
```

If the implementation of the chain walk changes, ideally only the machine proof establishing `recoverChain` needs to change.

The 42-chain proof should not depend on:

- exact instruction addresses;
- a particular register allocation;
- the precise instruction sequence;
- intermediate machine states that are irrelevant to the semantic result.

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

Its main potential value is data refinement between abstract XMSS objects and machine-level byte or limb representations.

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

A candidate is accepted only if it passes the proof and improves the benchmark.

---

## Benchmark model

The optimization objective must be explicit and reproducible.

### Ordinary instructions

Every executed ordinary RV instruction contributes according to one fixed virtual cycle model.

For the initial challenge, the simplest option is likely:

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

The exact number is configurable, but must be documented and constant across optimization runs.

The purpose is to optimize the verifier logic rather than the hash implementation.

### Artifact identity

The program being measured must be exactly the program being proved.

The benchmark tooling should make it difficult to accidentally:

- prove one bytecode artifact;
- measure another.

Ideally the same Lean program value, generated binary, or canonical byte sequence is consumed by both the proof and cycle evaluator.

---

## Repository constraints

These are known constraints of the current repository and dependency graph. They are not open design questions, but changes to dependencies or project structure must preserve them.

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

These are risks to the proof architecture or optimization experiment itself. They should influence implementation choices from the beginning.

### R1. Proofs may become coupled to exact bytecode

The optimization experiment depends on being able to change low-level RV code without rebuilding unrelated higher-level XMSS proofs.

A proof architecture that records long sequences of intermediate machine states, absolute instruction addresses, particular register allocations, or incidental implementation details will make automated optimization impractical.

**Mitigation:** expose stable semantic contracts at meaningful program boundaries, such as:

```text
recoverChain
recoverEndpoints
leafHash
decodeDigest
authenticationRoot
verify
```

Machine-level proofs establish these contracts. Higher-level proofs consume the contracts rather than reopening the underlying instruction sequence.

Prefer reusable local simplification lemmas, `simp`, `grind`, WP/decompilation rules, and frame lemmas over brittle instruction-by-instruction scripts.

**Early validation:** during M3, deliberately create a second implementation of `recoverChain` with a different instruction sequence and prove it against the same contract. The proof of code calling `recoverChain` should require no substantive change. If it does, fix the abstraction boundary before proceeding to M4.

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

Verification and rejection may follow different execution paths. Malformed or invalid inputs may also reject at different stages.

Therefore the performance objective must specify what is being optimized.

Possible metrics include:

```text
cost on valid verification
worst-case cost over permitted inputs
maximum rejection cost
a fixed benchmark corpus
```

For the initial challenge, prefer a metric that is deterministic and difficult for an optimizer to game. If valid verification has effectively fixed work because of the XMSS target-sum construction, document and prove the relevant fact rather than assuming it.

**Agent rule:** settle the benchmark path semantics before M9. Do not compare candidate programs using accidentally different execution paths.

### R4. The abstract hash boundary extends the execution model

Hashing is deliberately abstract, but an abstract hash call is not an ordinary RV64 instruction.

The proof must therefore distinguish clearly between:

1. execution justified by ordinary RV64 semantics; and
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

The authoritative Lean verifier is already `XmssSecurity.Concrete.verify`. The project should not create a second independent Lean implementation of XMSS.

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

rather than introducing serialization and decoding into the verifier unless byte-level parsing is intentionally part of the challenge.

A memory representation may use aligned fields and fixed offsets chosen for efficient RV execution.

**Agent rule:** keep representation predicates small and declarative. Do not introduce SSZ, frontend parsing, or a second `verifyBytes` algorithm unless the project explicitly decides that serialization itself should be optimized and proved.

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

Keep preconditions as strong as necessary for meaningful execution but no stronger than justified. Make observable behavior and frame conditions explicit.

Before M9, perform an adversarial review of the theorem and benchmark specifically asking:

> What incorrect or unintended program could still pass both gates?

### R9. Optimization-resilient abstractions may themselves hide performance

Semantic contracts are necessary for proof modularity, but they must not prevent the benchmark from observing the actual instructions executed inside a region.

The proof may reason abstractly about `recoverChain`; the evaluator must still execute and count the concrete RV implementation of `recoverChain`.

**Agent rule:** abstraction is for proofs, not execution. Do not replace optimized regions with uninterpreted semantic operations in the benchmark, except for the explicitly designated hash oracle.

### R10. Proof automation can become slow or unpredictable

Heavy use of `simp` and `grind` is useful only if the supporting lemma sets remain controlled.

Large global simp sets or overly broad automation can make proof checking slow, fragile, or sensitive to unrelated imports. That would be especially harmful once Lean becomes the inner correctness loop for automated optimization.

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
| **M8** | proof and evaluator demonstrably consume the same program artifact; benchmark semantics are documented |
| **M9** | adversarial review confirms that passing both gates captures the intended notion of a correct and improved candidate |

---

## Evaluation criteria

Correctness should be evaluated independently at three levels: the Lean proof itself, end-to-end executable behavior, and executable behavior of individual verifier components.

Passing `lake build` alone is not sufficient. The goal is to have independent checks that exercise both the formal theorem and the concrete RV execution.

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

The test corpus should include at least:

- valid accepting verifier inputs;
- validly encoded but rejecting inputs;
- modified signatures;
- modified public keys;
- modified authentication paths;
- boundary epoch values;
- zero-heavy and other simple edge-case values;
- deterministic pseudo-random structured inputs.

Tests should be reproducible. Randomized tests must therefore use a fixed seed or record their generated fixtures.

The differential test harness is not part of the trusted correctness argument. It is an independent engineering check intended to catch errors in theorem wiring, representation predicates, execution setup, and assumptions about the machine interface.

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

Every one should be exercised. Other inputs such as starting digests can use fixed edge cases plus deterministic pseudo-random values.

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
| **M3** | `recoverChain` differential tests, including all digit values `0..7` |
| **M4** | endpoint recovery and leaf-construction differential tests |
| **M5** | `TargetSum.decodeDigest` differential and boundary tests |
| **M6** | authentication-path differential tests covering both branch orderings |
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
    check that the theorem, machine setup, and spec are wired together correctly
             |
             v
component differential tests
    independently exercise and localize the concrete implementation
```

The Lean theorem is the actual correctness argument. Differential testing does not replace it.

Conversely, the existence of a proof should not be used as a reason to omit executable tests. The tests provide an independent check that the project has proved and executed the artifact it intended to build.

---

## Milestones

Each implementation milestone is complete only when its code, proof, executable tests, and cycle measurement are complete. A region that merely compiles or has a partial proof is not considered finished.

The milestones are deliberately ordered so that the risky architectural assumptions are tested early. By the end of M3, the project should have demonstrated the complete workflow on a small but real part of the verifier: write RV code, execute it, call the abstract hash oracle, prove it against the Lean specification, test it differentially, measure it, optimize it, and preserve its semantic contract.

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

The authoritative verifier specification remains `XmssSecurity.Concrete.verify`. Do not introduce a second independent Lean implementation of the verifier.

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

The theorem may contain `sorry` at this milestone. Its interface should be treated as stable once M2 begins.

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

The initial cost model should be simple and explicit. For example:

```text
ordinary executed RV instruction = 1 cycle
abstract hash call               = hashCost
```

where `hashCost` is one configurable parameter.

**Acceptance criteria:**

- abstract hash calls execute under the evaluator;
- their semantic contract is proved;
- tweak and payload construction has component-level tests;
- the evaluator deterministically reports executed instruction count, hash-call count, and total synthetic cost;
- the cost model is documented;
- proof and evaluator consume the same canonical program artifact;
- all E1 and applicable E3 evaluation gates pass.

---

### M3. `recoverChain` and proof-architecture validation

Implement and prove one complete WOTS chain walk.

For digit `x`, the region must perform exactly the semantic operation represented by the upstream `recoverChain`, including the remaining `7 - x` hash steps.

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

- `recoverChain` is proved correct;
- all digits `0..7` are differentially tested;
- two different implementations satisfy the same semantic contract;
- changing between those implementations does not require substantive changes to caller-level proofs;
- termination/frame behavior is proved;
- cycle counts are reported for both implementations;
- all E1 and applicable E3 gates pass.

**Stop condition:** if changing the implementation causes higher-level semantic reasoning to break, fix the proof boundary before beginning M4.

---

### M4. WOTS endpoint recovery and leaf construction

Use the M3 `recoverChain` contract to recover all 42 WOTS chain endpoints.

Then implement the leaf construction corresponding to the upstream specification.

Higher-level proofs must compose the M3 contract rather than reopen the concrete chain-walk instruction sequence.

**Acceptance criteria:**

- `recoverEndpoints` behavior is proved;
- leaf construction is proved against the corresponding Lean specification;
- component-level differential tests pass;
- the proof does not depend unnecessarily on the concrete implementation selected for `recoverChain`;
- termination and relevant frame properties are proved;
- cycle measurements are recorded;
- all E1 and applicable E3 gates pass.

---

### M5. Target-sum digest decoding

Implement and prove the RV equivalent of `TargetSum.decodeDigest`.

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

- the RV region is proved equivalent to `TargetSum.decodeDigest`;
- boundary and differential tests pass;
- rejection behavior agrees with the specification;
- proof automation remains suitable for repeated development;
- cycle measurement is recorded;
- all E1 and applicable E3 gates pass.

---

### M6. Merkle authentication path

Implement and prove the 32-level authentication-path computation corresponding to `authenticationRoot`.

For each level, the implementation must:

1. inspect the relevant epoch bit;
2. select the correct left/right child ordering;
3. construct the required hash input;
4. invoke the abstract hash;
5. continue with the resulting parent node.

Tests must exercise both left/right orderings and relevant epoch-bit boundaries.

The completed region should expose one stable `authenticationRoot` semantic contract to its callers.

**Acceptance criteria:**

- the 32-level computation is proved against the Lean specification;
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

Optimize the complete verifier and its component regions using the infrastructure established in M2 and validated in M3.

Every candidate must pass correctness before being considered a valid optimization:

```text
candidate
   |
   +---- proof/tests ---- fail ----> reject
   |
   +---- proof/tests ---- pass
                            |
                            v
                       measure cost
```

Track at least:

- static instruction count;
- executed ordinary RV instructions;
- abstract hash calls;
- total synthetic cost;
- proof-check time.

Maintain a reproducible baseline so every claimed improvement has a concrete comparison point.

Optimizations may alter instruction sequences, register allocation, control flow, or region implementations, but may not weaken the theorem or evaluation criteria.

**Acceptance criteria:**

- an explicit baseline is recorded;
- at least one nontrivial optimization is attempted;
- accepted optimized candidates pass the same E1, E2, and E3 gates as the baseline;
- performance comparisons use the same benchmark semantics;
- higher-level proofs remain insulated from local implementation changes where intended;
- benchmark results are reproducible.

---

### M9. Autoresearch harness

Package the proof and evaluation infrastructure so an untrusted automated agent can propose RV implementation changes and receive objective feedback.

The intended loop is:

```text
propose candidate
       |
       v
   Lean build
       |
       +---- fail -----------------> reject
       |
       v
differential tests
       |
       +---- fail -----------------> reject
       |
       v
 cycle evaluator
       |
       v
compare with baseline/best candidate
       |
       +---- no improvement -------> reject
       |
       v
      accept
```

The optimizer itself is not trusted.

Correctness comes from the same proof and evaluation gates used during manual development.

The harness should record enough information to reproduce every accepted result, including the program artifact and measured cost.

**Acceptance criteria:**

- one documented command runs the candidate evaluation pipeline;
- incorrect candidates cannot reach the performance-acceptance stage;
- proof, tests, and evaluator operate on the intended candidate artifact;
- accepted candidates and their measurements are reproducible;
- the best-known baseline and candidate costs are recorded;
- proof-check and evaluation latency are practical enough for repeated automated search.

---

## Milestone summary

| milestone | result |
|---|---|
| **M0** | repository and trust gates work |
| **M1** | machine/spec theorem boundary is fixed |
| **M2** | RV execution, abstract hashing, and cycle measurement work |
| **M3** | first real region is proved, tested, measured, and successfully optimized behind a stable contract |
| **M4** | all WOTS endpoints and leaf construction are verified |
| **M5** | target-sum decoding is verified |
| **M6** | Merkle authentication is verified |
| **M7** | complete RV verifier is proved equivalent to `Concrete.verify` |
| **M8** | verified optimization produces reproducible performance comparisons |
| **M9** | automated agents can safely search for better verified RV implementations |

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

The major loops are statically bounded: 42 WOTS chains, at most 7 remaining steps per chain, and 32 Merkle authentication levels.

The resulting **static program** is expected to be relatively small, plausibly on the order of hundreds of RV instructions. This is only a rough expectation and is not a design constraint.

The **dynamic executed instruction count** will be substantially larger because the loop bodies execute repeatedly during verification.

Do not optimize toward a predicted code size. Record the first straightforward proved implementation as the empirical baseline, then measure improvements from that baseline.

At minimum, report static instruction count, dynamically executed ordinary RV instructions, abstract hash-call count, and total synthetic cycle cost separately.

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
- re-proving the upstream XMSS security theorem;
- trusting the optimizer.

These can be layered on later without changing the core verifier theorem if the abstraction boundaries are chosen well.

---

## Done

- 2026-09-15: **M0** scaffold builds warning-free; both gates pass; `XmssSecurity.Scheme` elaborates on Lean v4.33.0 / VCVio `3ecd5523`; dependencies pinned on one toolchain.
- 2026-09-17: project direction clarified: pure virtual RV64, abstract hash oracle, byte-level verifier interface, proof-preserving optimization, deterministic cycle benchmark, no zkVM backend in the core project.