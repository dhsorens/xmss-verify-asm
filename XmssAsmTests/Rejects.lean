/-
  XmssAsmTests.Rejects -- the reject archive.

  There is one verifier program on `main`. The no-alternates rule bans a live
  alternate `Program` a caller could select; it does not ban recording what
  went wrong. A candidate that failed for a reason worth remembering is kept
  here as an instruction list plus the failure it is expected to produce, and
  this suite asserts it *still* fails for that reason -- so if a reject ever
  starts passing, that is news, and the suite says so rather than going quiet.

  These lists are test data. Nothing outside this file refers to them, they are
  never reachable from `verifier`, and `verifierWithWalk` exists only here --
  the shipping harness deliberately has no `code` parameter, so that it cannot
  silently measure a program the theorem is not about.

  Why keep them. Each records a rejection that a plausible optimizer would
  have to rediscover:

  * `noHeaderGuard` -- the header `BGE` is the loop's only exit. Removing it
    looks like one free instruction per chain and loses termination outright.
    This is what the fuel filter is for;
  * `hoistedTweak` -- the tweak word depends on the chain position, so
    hoisting its store out of the loop is not value-preserving. It saves one
    instruction per step and computes the wrong chain. Only the differential
    suite says so; the proofs would simply fail to close, and a candidate
    generator that never ran them would call this a win;
  * `shortBound` -- a bound of `8 i + 6` instead of `8 i + 7` stops each chain
    one step early. It is *faster on the score* (3209 steps against 3434 on
    `valid-epmax`) and wrong. Nothing in the step count rejects it: only the
    exact hash pin does, which is why the pin is an equality and not a bound.
    This is the most useful entry in the file.
-/

import XmssAsmTests.Fixtures
import XmssAsm.Machine.Eval
import XmssAsm.Contract

namespace XmssAsm.Tests

open XmssAsm RiscvZkvm.Rv64 XmssSecurity

/-- The verifier with the chain walk replaced, with the chains loop's back
    branch recomputed for the candidate's length. Test data only. -/
def verifierWithWalk (w : Program) : Program :=
  let body := chainLoad ++ w ++ chainStore
  init ++ decode ++ (chainsPre ++ (body ++ [.BNE .x13 .x6 (bOff (-(4 * body.length)))])) ++
    leaf ++ auth ++ final

def codeWithWalk (w : Program) : CodeMem := loadProgram CODE_BASE (verifierWithWalk w)

/-- How a recorded candidate is expected to fail. -/
inductive RejectKind where
  /-- Fuel exhausted or trapped: the run does not reach a halt. -/
  | noHalt
  /-- Halts, keeps the hash pin, and reports the wrong answer. -/
  | wrongResult
  /-- Halts and makes the wrong number of oracle calls. -/
  | hashCount
  deriving Repr, DecidableEq

structure Reject where
  name : String
  /-- Why it is worth remembering. -/
  why : String
  walk : Program
  kind : RejectKind

/-! ## The archive -/

/-- The header `BGE` removed: the back jump now targets the first step of the
    body, so nothing ever leaves the loop. -/
def walkNoHeaderGuard : Program :=
  [.LI .x7 BUFA, .LI .x5 HASH_ID, .LI .x10 BUFA, .LI .x11 48, .LI .x12 CUR,
   .SLLI .x6 .x8 32, .SD .x7 .x6 8, .ADD .x15 .x16 .x14, .ADDI .x17 .x16 7] ++
  chainStep ++ [.JAL .x0 (jOff (-(4 * chainStep.length)))]

/-- The tweak store hoisted into the prologue. Every step after the first
    hashes under the position of the first. -/
def walkHoistedTweak : Program :=
  [.LI .x7 BUFA, .LI .x5 HASH_ID, .LI .x10 BUFA, .LI .x11 48, .LI .x12 CUR,
   .SLLI .x6 .x8 32, .SD .x7 .x6 8, .ADD .x15 .x16 .x14, .ADDI .x17 .x16 7,
   .SLLI .x6 .x15 32, .ADDI .x6 .x6 0x100, .SD .x7 .x6 0,
   .BGE .x15 .x17 (bOff 16)] ++
  [.ECALL, .ADDI .x15 .x15 1] ++ [.JAL .x0 (jOff (-12))]

/-- The chain bound one short: `8 i + 6` instead of `8 i + 7`. Faster on the
    score, one hash short on every chain that still had work, and wrong. -/
def walkShortBound : Program :=
  [.LI .x7 BUFA, .LI .x5 HASH_ID, .LI .x10 BUFA, .LI .x11 48, .LI .x12 CUR,
   .SLLI .x6 .x8 32, .SD .x7 .x6 8, .ADD .x15 .x16 .x14, .ADDI .x17 .x16 6,
   .BGE .x15 .x17 (bOff (4 * (chainStep.length + 2)))] ++
  chainStep ++ [.JAL .x0 (jOff (-(4 * (chainStep.length + 1))))]

def rejects : List Reject :=
  [{ name := "noHeaderGuard"
     why := "the header BGE is the loop's only exit; removing it loses termination"
     walk := walkNoHeaderGuard, kind := .noHalt },
   { name := "hoistedTweak"
     why := "the tweak word depends on the position, so hoisting its store is not \
             value-preserving"
     walk := walkHoistedTweak, kind := .wrongResult },
   { name := "shortBound"
     why := "one hash short per chain: faster on the score, and wrong -- this is why \
             the hash count is an exact pin"
     walk := walkShortBound, kind := .hashCount }]

/-! ## The assertion

Each recorded candidate is run on an accepting fixture. The suite fails if a
recorded reject *passes* -- that would mean the archive is stale, or that a
change to the machine or the surrounding regions made a rejected candidate
viable and it should be re-judged by the accept gate rather than sitting here. -/

/-- Fuel for a recorded walk. Far smaller than `verifierFuel`, because a
    correct accepting run is about 3,400 steps, so exhausting 8,000 is already
    decisive -- and because `noHeaderGuard` does not terminate, so every step
    of its budget is paid on every run of the suite. -/
def rejectFuel : Nat := 8000

/-- The observed failure of a recorded walk on an accepting fixture. -/
def runReject (w : Program) (f : Fixture) : Option RejectKind × Stats × Word :=
  let s := { initState f.pk f.ep f.msg f.sig with code := codeWithWalk w }
  let (s', st, stop) := runH H_test rejectFuel s {}
  let a0 := s'.getReg .x10
  if stop != Stop.halted then (some .noHalt, st, a0)
  else if st.hashes != 133 then (some .hashCount, st, a0)
  else if a0 != resultWord f.expected then (some .wrongResult, st, a0)
  else (none, st, a0)

def checkReject (r : Reject) (f : Fixture) : Option String × Stats :=
  match runReject r.walk f with
  | (none, st, a0) =>
    (some s!"reject {r.name}: PASSED on {f.name} (a0={a0.toNat}, {st.steps} steps, \
       {st.hashes} hashes). It was rejected because {r.why}; if that no longer holds, \
       judge it with scripts/accept.sh instead of leaving it here.", st)
  | (some k, st, _) =>
    if k == r.kind then (none, st)
    else
      (some s!"reject {r.name}: fails as {repr k}, archived as {repr r.kind}. The recorded \
         reason ({r.why}) no longer describes what happens.", st)

/-- The fixture the archive is judged on: an accepting one, since a rejecting
    fixture would agree with a broken walk by accident. -/
def rejectFixture : Option Fixture := corpus.find? (fun f => f.name == "valid-epmax")

end XmssAsm.Tests
