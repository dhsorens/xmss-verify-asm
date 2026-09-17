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
  the benchmark rather than the theorem (PLAN R8).
* `stepH` traps on an out-of-range hash call, so termination forces every
  call's buffers to be valid memory.

*What an incorrect program could still do while passing both gates?* It could
be slow, or compute the right answer by a different route (e.g. a different
layout of the same hash inputs). Both are permitted; the benchmark ranks them.
