# Agent conventions — xmss-asm

Standing rules. **Start at `PLAN.md`** each session: the queue and the open
decisions. Neither it nor `README.md` is frozen.

## Ownership

- **None of the frameworks live here.** `RiscvZkvm.*` (machine), `Decomp.*`
  (decompilation), `Refine.*` (refinement) and `XmssSecurity.*` (spec) all
  arrive under `.lake/packages/`. Read them there; **never edit them from
  here** — a change is a PR against that repository, then `lake update <dep>`.
- Before adding anything abstract, ask which repository owns it. Names neither
  a machine nor XMSS: `lean-refine`. Names a machine but not XMSS:
  `riscv-decomp`. Names XMSS but not a machine: it is the spec's, and if the
  spec is wrong that is a leanVM issue, not a local patch. Names both: here.
- Mathlib: targeted `import Mathlib.<Module>` only, never `import Mathlib`.

## Proof hygiene

- Never introduce an `axiom`. Unfinished proofs use `sorry` (grep-able).
- No `native_decide` / `bv_decide` (`scripts/check-forbidden-tactics.sh`).
- Unused hypotheses mean the theorem is not tight — drop them.
- Keep layers distinct: spec / algorithm / decompiled function / machine. A
  theorem that mentions both `Concrete.verify` and `MachineState` outside the
  bridge means the abstraction has collapsed.
- A green proof of a weak statement is not progress. Prefer, in order: a real
  semantic disagreement; a vacuous or false guarantee; a blind spot in the
  model or observation; a meaningful theorem with an explicit trust base; an
  honest unknown.
- Proof-facing code data is `Program` literals. Hex words are not proof objects.

## Module system

`module` files may import only `XmssAsm.Upstream` and other modules. Anything
touching `Refine.*` or `XmssSecurity.*` is a legacy file. Do not "fix" this by
copying upstream definitions into a module.

## Build discipline

`lake build` must stay warning-free. Run both gates before claiming a slice
done. Do not commit `lake-manifest.json` changes without saying which pin
moved and why.
