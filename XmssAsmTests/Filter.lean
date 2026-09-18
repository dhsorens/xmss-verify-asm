/-
  XmssAsmTests.Filter -- `lake exe filter`, the inner loop of PLAN M9.

  The cheap, untrusted filter. It runs the candidate program through the
  interpreter and rejects obvious losers *without* checking any proof: the
  chain walk in isolation for every digit, the whole fixture corpus
  end-to-end, the hash pin, and the score.

  What makes it cheap is the import list. This module imports the fixtures,
  the evaluator and the representation, and no region proof, so it builds and
  runs while `XmssAsm/Regions/Chain.lean` is still broken. That is the point:
  a candidate that computes the wrong chain should cost seconds to reject, not
  a full proof check.

  It is emphatically **not** a merge gate. Passing here means only that the
  candidate is worth paying the proof check for. Landing is
  `scripts/accept.sh`, and the Lean kernel is the trust boundary. A green
  filter on a candidate whose `chainWalk_correct` does not close is a reject.
-/

import XmssAsmTests.Fixtures
import XmssAsm.Machine.Eval
import XmssAsm.Contract

namespace XmssAsm.Tests

open XmssAsm RiscvZkvm.Rv64 XmssSecurity

/-- Run until the pc is `target`, counting steps and hashes. A local copy:
    the filter must not import the region test harness, which imports the
    region proofs. -/
def filterUntil (H : List UInt8 → BitVec 256) :
    Nat → MachineState → Word → Stats → MachineState × Stats × Bool
  | 0, s, _, st => (s, st, false)
  | fuel + 1, s, target, st =>
    if s.pc == target then (s, st, true) else
    match stepH H s with
    | none => (s, st, false)
    | some s' =>
      filterUntil H fuel s' target
        { steps := st.steps + 1, hashes := st.hashes + (if isHashCall s then 1 else 0) }

def filterFuel : Nat := 20000

/-! ## Filter 1: the chain walk in isolation, every digit

The walk's entry state, built from `ChainWalkPre`: the digit in `x14`, the
chain index scaled in `x16`, the epoch in `x8`, `P` at `BUFA_P` and the
starting value at `CUR`. Registers and memory start at a sentinel so that a
walk which reads something it should not is likely to produce nonsense rather
than a plausible zero. -/
def filterChainState (P : PublicParameter) (ep : Epoch) (i : ChainIndex) (x : Digit)
    (v : Digest) : MachineState :=
  let s : MachineState :=
    { regs := fun _ => 0xDEADBEEF#64, mem := fun a => 0xC0FFEE00#64 + a,
      code := verifierCode, pc := addr idxChainWalk }
  let s := (s.setReg .x8 (BitVec.ofNat 64 ep.val)).setReg .x14 (BitVec.ofNat 64 x.val)
  let s := (s.setReg .x16 (BitVec.ofNat 64 (8 * i.val))).setReg .x13 (BitVec.ofNat 64 i.val)
  (s.writeWords BUFA_P [dLo P, dHi P]).writeWords CUR [dLo v, dHi v]

def filterDigest (s : MachineState) (a : Word) : Digest :=
  digestOfWords (s.getMem a) (s.getMem (a + 8))

/-- One digit of the chain walk against `Concrete.recoverChain`. -/
def filterChain (xn : Nat) : Option String × Stats :=
  let x : Digit := ⟨xn % 8, Nat.mod_lt _ (by decide)⟩
  let P : PublicParameter := BitVec.ofNat 128 (0xA5A5 * (xn + 1))
  let ep : Epoch := ⟨(0x1234567 * (xn + 3)) % 2 ^ 32, Nat.mod_lt _ (by decide)⟩
  let i : ChainIndex := ⟨(7 * xn + 1) % 42, Nat.mod_lt _ (by decide)⟩
  let v : Digest := BitVec.ofNat 128 (0x5EED * (xn + 11))
  let s := filterChainState P ep i x v
  let (s', st, reached) := filterUntil H_test filterFuel s (addr idxChainStore) {}
  if !reached then
    (some s!"chain digit {x.val}: the walk did not reach idxChainStore in {filterFuel} steps", st)
  else
    let got := filterDigest s' CUR
    let want := evalD (Concrete.recoverChain P ep i x v)
    if got != want then (some s!"chain digit {x.val}: CUR is wrong after the walk", st)
    else if st.hashes != 7 - x.val then
      (some s!"chain digit {x.val}: {st.hashes} hashes, the chain needs {7 - x.val}", st)
    else (none, st)

/-! ## Filter 2: the corpus end-to-end, and the score -/

def filterRun (f : Fixture) : Bool × Word × Stats :=
  let s := initState f.pk f.ep f.msg f.sig
  let (s', st, stop) := runH H_test verifierFuel s {}
  (stop == Stop.halted, s'.getReg .x10, st)

def filterOts (f : Fixture) : Option (Nat × Nat) :=
  let s := initState f.pk f.ep f.msg f.sig
  let (_, st, reached) := filterUntil H_test filterFuel s (addr idxAuth) {}
  if reached then some (st.steps, st.hashes) else none

end XmssAsm.Tests

open XmssAsm XmssAsm.Tests

def main : IO UInt32 := do
  IO.println "== xmss-asm inner filter (no proof is checked here) =="
  let mut failures := 0
  IO.println "-- the chain walk in isolation, digits 0..7"
  for xn in List.range 8 do
    match filterChain xn with
    | (some msg, _) => failures := failures + 1; IO.println s!"FAIL {msg}"
    | (none, st) => IO.println s!"ok   digit {xn}: steps={st.steps} hashes={st.hashes}"
  IO.println "-- the corpus end-to-end"
  let mut n := 0
  for f in corpus do
    let (halted, a0, _) := filterRun f
    if halted && a0 == resultWord f.expected then n := n + 1
    else
      failures := failures + 1
      IO.println s!"FAIL {f.name}: halted={halted} a0={a0.toNat}, spec says {f.expected}"
  IO.println s!"ok   {n} of {corpus.length} fixtures agree with the specification"
  IO.println "-- the hash pin and the score"
  let accepting := corpus.filter (fun f => f.expected)
  let mut otsSteps : List Nat := []
  for f in accepting do
    match filterOts f with
    | none => failures := failures + 1; IO.println s!"FAIL {f.name}: did not reach the OTS cut"
    | some (st, h) =>
      otsSteps := st :: otsSteps
      if h != 101 then
        failures := failures + 1
        IO.println s!"FAIL {f.name}: {h} OTS hashes, the pin is 101"
  if otsSteps.eraseDups.length != 1 then
    failures := failures + 1
    IO.println s!"FAIL OTS steps vary across accepting fixtures: {otsSteps.eraseDups}"
  match accepting.find? (fun f => f.name == "valid-epmax") with
  | none => failures := failures + 1; IO.println "FAIL fixture valid-epmax is missing"
  | some f =>
    let (halted, _, st) := filterRun f
    if !halted || st.hashes != 133 then
      failures := failures + 1
      IO.println s!"FAIL valid-epmax: halted={halted}, {st.hashes} hashes, the pin is 133"
    else
      IO.println s!"ok   hash pin held; m = ({otsSteps.head?.getD 0}, {st.steps})"
  if failures = 0 then
    IO.println "filter: PASS -- worth paying the proof check for (scripts/accept.sh)"
    return 0
  IO.println s!"filter: REJECT -- {failures} failure(s); no proof was checked"
  return 1
