/-
  XmssAsmTests.Main -- `lake exe difftest`

  Runs the end-to-end differential corpus and prints the cycle report for the
  valid fixtures. Exit code 1 on any disagreement.
-/

import XmssAsmTests

open XmssAsm XmssAsm.Tests

def main (args : List String) : IO UInt32 := do
  let hashCost := (args.head? >>= String.toNat?).getD defaultHashCost
  IO.println s!"== xmss-asm differential test (hash cost = {hashCost}) =="
  IO.println s!"static instruction count: {staticInstructionCount}"
  let mut failures := 0
  let mut n := 0
  for f in corpus do
    n := n + 1
    let (err, r) := checkFixture f
    match err with
    | some msg => failures := failures + 1; IO.println s!"FAIL {msg}"
    | none =>
      IO.println s!"ok   {f.name}: a0={r.a0.toNat} steps={r.stats.steps} hashes={r.stats.hashes} \
        ordinary={r.stats.ordinary} cost={r.stats.cost hashCost}"
  IO.println s!"{n} fixtures, {failures} failures"
  return if failures = 0 then 0 else 1
