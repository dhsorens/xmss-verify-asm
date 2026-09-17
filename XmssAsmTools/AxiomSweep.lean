/-
  XmssAsmTools.AxiomSweep -- kernel-truth axiom gate for this repository's own Lean.

  Ported from `riscv-decomp`'s `DecompTools/AxiomSweep.lean`, which audits *its*
  libraries and says nothing about ours. A **policy** gate rather than a
  name-by-name baseline: walk every declaration under the audited prefixes,
  collect its axiom dependencies, and fail if anything outside the documented
  set appears. It complements `scripts/check-forbidden-tactics.sh` (a fast
  source scan) by reading what the kernel actually recorded, so it also catches
  a `sorry`, a forbidden tactic behind a macro, and any new axiom a dependency
  pin bump drags into our proofs.

  Run after `lake build`; it imports the built oleans.

    lake build axiomsweep
    .lake/build/bin/axiomsweep            # enforce
    .lake/build/bin/axiomsweep --report   # print the census, exit 0

  `scripts/check-axioms.sh` is the wrapper.
-/

module

public import Lean

@[expose] public section

open Lean

/-- Declarations under these prefixes are audited: everything this repository
    owns. -/
def scanPrefixes : List Name := [`XmssAsm, `XmssAsmTools]

/-- Modules to import. These two roots transitively cover the whole owned
    tree. -/
def scanModules : Array Import :=
  #[{ module := `XmssAsm }, { module := `XmssAsmTools }]

/-- The axioms this repository accepts. Lean's three classical axioms and
    nothing else; change this list only alongside README "Trust". Note what is
    **not** here: `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, and the
    four Sail platform axioms `riscv-zkvm`'s generated extraction declares --
    nothing we prove should reach the `SailEquiv` layer. -/
def allowedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

def isScanned (n : Name) : Bool :=
  scanPrefixes.any (fun p => p.isPrefixOf n) && !n.isInternal

def main (args : List String) : IO UInt32 := do
  let report := args.contains "--report"
  initSearchPath (← findSysroot)
  let env ← importModules scanModules {} (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<axiomsweep>", fileMap := default }
  let state : Core.State := { env }

  let run : CoreM (Nat × NameMap (Array Name) × NameMap (Array Name)) := do
    let mut audited := 0
    let mut offenders : NameMap (Array Name) := {}
    let mut census : NameMap (Array Name) := {}
    for (n, _) in (← getEnv).constants.toList do
      unless isScanned n do continue
      audited := audited + 1
      let axs ← collectAxioms n
      unless axs.isEmpty do census := census.insert n axs
      let bad := axs.filter (fun a => !allowedAxioms.contains a)
      unless bad.isEmpty do offenders := offenders.insert n bad
    return (audited, offenders, census)

  let ((audited, offenders, census), _) ← run.toIO ctx state

  let offList := offenders.toList
  if report then
    IO.println s!"== Axiom sweep over {scanPrefixes} =="
    IO.println s!"   declarations audited:        {audited}"
    IO.println s!"   resting on some axiom:       {census.toList.length}"
    IO.println s!"   allowed axioms:              {allowedAxioms}"
    for a in allowedAxioms do
      let uses := census.toList.filter (fun (_, axs) => axs.contains a)
      IO.println s!"     {a}: {uses.length} declaration(s)"
    IO.println s!"   offenders:                   {offList.length}"
    for (n, axs) in offList do
      IO.println s!"     {n}: {axs.toList}"
    IO.println "\n(report mode -- exit 0)"
    return 0

  if offList.isEmpty then
    IO.println s!"axiomsweep: OK -- {audited} declarations rest only on the \
      {allowedAxioms.length} documented axioms."
    return 0

  IO.eprintln "axiomsweep FAILED: declaration(s) depend on an undocumented axiom:"
  for (n, axs) in offList do
    IO.eprintln s!"  {n}"
    IO.eprintln s!"    {axs.toList}"
  IO.eprintln "\nIf this is `sorryAx`, a proof is incomplete -- allowed while it is \
    grep-able, but not in a gated build. If it is `Lean.ofReduceBool` / \
    `Lean.trustCompiler`, a TCB-expanding tactic got in (see \
    scripts/check-forbidden-tactics.sh). If a pin bump introduced a new axiom, \
    add it to `allowedAxioms` AND to the README's Trust section, in the same change."
  return 1
