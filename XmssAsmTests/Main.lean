/-
  XmssAsmTests.Main -- `lake exe difftest`

  Runs the component suites (byte bridge, chain region for both
  implementations), the end-to-end differential corpus on the artifact and on
  the implementation-B build, and prints the cycle reports. Exit code 1 on
  any disagreement.
-/

import XmssAsmTests

open XmssAsm XmssAsm.Tests

def main (args : List String) : IO UInt32 := do
  let hashCost := (args.head? >>= String.toNat?).getD defaultHashCost
  IO.println s!"== xmss-asm differential test (hash cost = {hashCost}) =="
  IO.println s!"static instruction count: {staticInstructionCount} (implementation B build: {verifierB.length})"
  let mut failures := 0
  IO.println "-- component checks: byte-level bridge"
  for (name, ok) in componentChecks do
    if ok then IO.println s!"ok   {name}"
    else
      failures := failures + 1
      IO.println s!"FAIL {name}"
  IO.println "-- component checks: chain walk, digits 0..7, implementations A and B"
  let mut nChain := 0
  for impl in [implA, implB] do
    for c in chainCorpus do
      nChain := nChain + 1
      match checkChain impl c with
      | (some msg, _) => failures := failures + 1; IO.println s!"FAIL {msg}"
      | (none, _) => pure ()
  IO.println s!"{nChain} chain cases run"
  IO.println "-- chain walk cycles per digit (steps / hashes), starting digest 0"
  let cyA := chainCycles implA
  let cyB := chainCycles implB
  for ((x, a), (_, b)) in cyA.zip cyB do
    IO.println s!"digit {x}: A steps={a.steps} hashes={a.hashes} cost={a.cost hashCost} | \
      B steps={b.steps} hashes={b.hashes} cost={b.cost hashCost}"
  IO.println "-- end-to-end corpus, artifact (implementation A)"
  let mut n := 0
  for f in corpus do
    n := n + 1
    let (err, r) := checkFixture f
    match err with
    | some msg => failures := failures + 1; IO.println s!"FAIL {msg}"
    | none =>
      IO.println s!"ok   {f.name}: a0={r.a0.toNat} steps={r.stats.steps} hashes={r.stats.hashes} \
        ordinary={r.stats.ordinary} cost={r.stats.cost hashCost}"
  IO.println "-- end-to-end corpus, implementation B build"
  let mut nB := 0
  for f in corpus do
    nB := nB + 1
    let (err, r) := checkFixtureWith verifierCodeB f
    match err with
    | some msg => failures := failures + 1; IO.println s!"FAIL [B] {msg}"
    | none =>
      if r.a0 == 1 then
        IO.println s!"ok   [B] {f.name}: steps={r.stats.steps} hashes={r.stats.hashes} \
          ordinary={r.stats.ordinary} cost={r.stats.cost hashCost}"
  IO.println s!"{n} fixtures (A), {nB} fixtures (B), {nChain} chain cases, {componentChecks.length} bridge checks, {failures} failures"
  return if failures = 0 then 0 else 1
