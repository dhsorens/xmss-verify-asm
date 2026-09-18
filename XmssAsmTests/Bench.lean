/-
  XmssAsmTests.Bench -- `lake exe bench`

  The machine-readable metric dump the accept gate scores a candidate from.
  One `KEY=VALUE` line per metric, the same format as
  `bench/baseline.txt`, so `scripts/accept.sh` can compare the two without a
  parser.

  The score is the lexicographic pair `(OTS_STEPS, XMSS_EPMAX_STEPS)`. Hash
  counts are an exact pin, not a score term. Everything else printed here is
  reported, not scored: static size is a tie-break at most, and
  `AUTH_EPMAX_STEPS` is here because `XmssAsm.Regions.AuthCost` proves what it
  must be.

  `OTS_STEPS_DISTINCT` is the OTS-constancy assertion in numeric form. OTS
  cost is the same on every accepting fixture for *this* program because the
  target sum forces the chain work, but that is not true of every candidate --
  a digit-dependent fast path would break it and make "OTS steps on an
  accepting path" ambiguous. The gate requires this to be `1`.
-/

import XmssAsmTests

open XmssAsm XmssAsm.Tests RiscvZkvm.Rv64 XmssSecurity

/-- The worst-case accepting XMSS run: the all-ones epoch, which
    `XmssAsm.authSteps_lt_of_ne` shows is the unique maximum. -/
def epmaxName : String := "valid-epmax"

/-- The measured program, one instruction per line, for the record file. A
    record has to be reproducible from what is written down, and the commit
    plus this listing is that. -/
def printProgram : IO Unit := do
  IO.println s!"# {verifier.length} instructions, loaded at CODE_BASE"
  let mut i := 0
  for ins in verifier do
    IO.println s!"{i} {repr ins}"
    i := i + 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--program" then printProgram; return 0
  let accepting := corpus.filter (fun f => f.expected)
  let mut errs : List String := []
  -- OTS leg: init + decode + 42 chains + leaf, stopping at the semantic cut
  -- (after the leaf hash, before the first authentication instruction).
  let mut otsSteps : List Nat := []
  let mut otsHashes : List Nat := []
  for f in accepting do
    match XmssAsm.Tests.otsSteps f, hashSplit f with
    | some st, some (h, _) => otsSteps := st :: otsSteps; otsHashes := h :: otsHashes
    | _, _ => errs := s!"{f.name}: did not reach the OTS cut" :: errs
  let distinctOts := otsSteps.eraseDups.length
  let distinctOtsH := otsHashes.eraseDups.length
  -- the worst-case accepting XMSS run
  let epmax := accepting.find? (fun f => f.name == epmaxName)
  match epmax with
  | none => errs := s!"fixture {epmaxName} is missing from the corpus" :: errs
  | some f =>
    let r := runFixture f
    unless r.halted && r.a0 == 1 do
      errs := s!"{epmaxName}: halted={r.halted} a0={r.a0.toNat}, expected an accept" :: errs
  let epmaxSteps := (epmax.map (fun f => (runFixture f).stats.steps)).getD 0
  let epmaxHashes := (epmax.map (fun f => (runFixture f).stats.hashes)).getD 0
  let authSteps := (epmax.bind authLeg).map Prod.fst
  IO.println s!"# xmss-asm metric dump; score = (OTS_STEPS, XMSS_EPMAX_STEPS), lexicographic"
  IO.println s!"OTS_STEPS={otsSteps.head?.getD 0}"
  IO.println s!"OTS_HASHES={otsHashes.head?.getD 0}"
  IO.println s!"OTS_STEPS_DISTINCT={distinctOts}"
  IO.println s!"OTS_HASHES_DISTINCT={distinctOtsH}"
  IO.println s!"XMSS_EPMAX_STEPS={epmaxSteps}"
  IO.println s!"XMSS_EPMAX_HASHES={epmaxHashes}"
  IO.println s!"AUTH_EPMAX_STEPS={(authSteps.getD 0)}"
  IO.println s!"STATIC_INSTRUCTIONS={staticInstructionCount}"
  IO.println s!"ACCEPTING_FIXTURES={accepting.length}"
  IO.println s!"CORPUS_FIXTURES={corpus.length}"
  if errs.isEmpty then return 0
  for e in errs.reverse do IO.eprintln s!"bench FAILED: {e}"
  return 1
