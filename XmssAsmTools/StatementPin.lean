/-
  XmssAsmTools.StatementPin -- statement integrity for the optimization gate.

  The threat this closes, and why it runs before anything expensive. A
  candidate that *weakens the statement* -- adds a hypothesis to
  `VerifierCorrect`,
  drops a conjunct from `Represents`, widens the frame, moves an input
  address, or redefines what a hash `ECALL` does -- builds cleanly, passes the
  axiom sweep, passes every differential fixture, and scores better. Nothing
  else in the gate catches it.

  So the gate pins the *meaning* of the frozen vocabulary rather than the
  bytes of the files that hold it. This tool prints, for a documented list of
  constants, the elaborated type of each and (for definitions, not theorems)
  its elaborated value. `scripts/accept.sh` hashes that output and compares it
  to `bench/statement.sha256`.

  What is deliberately NOT pinned: `verifier`, `verifierCode`, the region
  programs and every index and offset derived from them. Those are exactly
  what a candidate is allowed to change, which is why pinning whole source
  files would not work.

  A missing constant is a failure, not a skip: inlining `Represents` into the
  contract would otherwise pass.

    lake build statementpin
    lake env ./.lake/build/bin/statementpin            # print the pinned forms
    lake env ./.lake/build/bin/statementpin --names    # just the list

  Re-pinning is a human action, in its own commit: a toolchain bump can move
  the pretty-printer's output without any change in meaning.
-/

module

public import Lean

@[expose] public section

open Lean Meta

/-- **The frozen vocabulary.** These are `Name` literals rather than resolved
    constants (`XmssAsmTools` does not import `XmssAsm`, so that a broken proof
    cannot break the gate that judges it); a name that does not resolve is
    reported as `MISSING` and fails the tool.

    Grouped as the optimization contract groups it: Grouped as the optimization contract groups it:
    the theorem statement, the input representation, the memory layout and the
    hash-oracle semantics. Adding to this list tightens the gate; removing
    from it loosens the gate, and is a human decision. -/
def pinnedConsts : List Name :=
  -- the statement
  [`XmssAsm.VerifierCorrect, `XmssAsm.xmss_verify_correct, `XmssAsm.resultWord,
   `XmssAsm.evalH,
  -- the input representation
   `XmssAsm.Represents, `XmssAsm.digestWords, `XmssAsm.initState, `XmssAsm.blankState,
   `XmssAsm.HasDigest, `XmssAsm.HasMessage, `XmssAsm.HasRandomness,
   `XmssAsm.dLo, `XmssAsm.dHi, `XmssAsm.digestOfWords, `XmssAsm.mW, `XmssAsm.rW,
  -- the memory layout and the frame
   `XmssAsm.ROOT, `XmssAsm.PARAM, `XmssAsm.EPOCH, `XmssAsm.MSG, `XmssAsm.RHO,
   `XmssAsm.CHAINS, `XmssAsm.AUTH, `XmssAsm.SCRATCH_LO, `XmssAsm.SCRATCH_HI,
   `XmssAsm.CODE_BASE, `XmssAsm.InScratch, `XmssAsm.InRange, `XmssAsm.CLOB,
   `XmssAsm.Frame,
  -- the hash-oracle semantics
   `XmssAsm.HASH_ID, `XmssAsm.outWords, `XmssAsm.hashInputOf, `XmssAsm.outBlockValid,
   `XmssAsm.hashArgsValid, `XmssAsm.hashEffect, `XmssAsm.AtHashCall, `XmssAsm.stepH,
   `XmssAsm.hashStepper, `XmssAsm.Reaches, `XmssAsm.Runs,
  -- the benchmark: what the evaluator counts, what the fixtures expect, and the
  -- claim the differential harness checks. These live on denied paths, but the
  -- denylist is a diff check and this is the environment: a candidate that
  -- reaches them some other way still has to match here.
   `XmssAsm.runH, `XmssAsm.isHalted, `XmssAsm.isHashCall, `XmssAsm.Stats.cost,
   `XmssAsm.staticInstructionCount, `XmssAsm.specVerify, `XmssAsm.specVerify_eq,
   `XmssAsm.initState_verify]

/-- Pretty-printer settings the pin is taken under. Fixed here so that a
    `set_option` elsewhere cannot change the hash. -/
def pinOptions : Options :=
  (((({} : Options).setBool `pp.fullNames true).setBool `pp.piBinderTypes true).setBool
    `pp.funBinderTypes true).setBool `pp.coercions true

def main (args : List String) : IO UInt32 := do
  if args.contains "--names" then
    for n in pinnedConsts do IO.println n
    return 0
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `XmssAsm }] {} (trustLevel := 1024)
  let ctx : Core.Context :=
    { fileName := "<statementpin>", fileMap := default, options := pinOptions }
  let state : Core.State := { env }
  let run : CoreM (Array String × Nat) := MetaM.run' do
    let mut out := #[]
    let mut missing := 0
    for n in pinnedConsts do
      match (← getEnv).find? n with
      | none =>
        missing := missing + 1
        out := out.push s!"{n} :: MISSING"
      | some ci =>
        out := out.push s!"{n} : {(← ppExpr ci.type).pretty 100}"
        match ci with
        | .thmInfo _ => out := out.push s!"{n} := <proof, not pinned>"
        | _ => match ci.value? with
          | some v => out := out.push s!"{n} := {(← ppExpr v).pretty 100}"
          | none => out := out.push s!"{n} := <no value>"
    return (out, missing)
  let ((lines, missing), _) ← run.toIO ctx state
  IO.println s!"-- statement pin over {pinnedConsts.length} frozen constants"
  for l in lines do IO.println l
  if missing != 0 then
    IO.eprintln s!"statementpin FAILED: {missing} pinned constant(s) missing from the \
      environment. A frozen definition was deleted or renamed -- possibly inlined into \
      its caller, which the hash alone would not catch."
    return 1
  return 0
