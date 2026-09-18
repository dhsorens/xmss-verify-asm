/-
  XmssAsmTests.Cost

  The cost theorems, checked against the machine.

  `XmssAsm.Regions.AuthCost` proves that the authentication path costs
  `1090 + 3 * popcount32 ep` steps. That is a statement about the loaded
  program, so it is also a prediction about what the interpreter will count.
  This file runs each accepting fixture to the region boundaries and asserts
  the two agree exactly. The point is to keep a proof and a measurement that
  *can* disagree, wired so that a disagreement fails the suite: a cost theorem
  nothing executes is a theorem about a program no one measured.

  It also records the pinned hash counts. The benchmark's score is a step
  count; the hash count is an *equality* assertion, so a candidate that wins
  by hashing fewer times -- that is, by computing something else -- fails the
  gate rather than setting a record.
-/

import XmssAsmTests.Regions
import XmssAsm.Regions.AuthCost

namespace XmssAsm.Tests

open XmssAsm RiscvZkvm.Rv64 XmssSecurity

/-- Fuel for one region leg; the whole verifier is under 4000 steps. -/
def legFuel : Nat := 100000

/-- Steps the machine actually takes from `idxAuth` to `idxFinal`, and the
    hashes it charges on the way, on a fixture that reaches both. -/
def authLeg (f : Fixture) : Option (Nat × Nat) :=
  let s0 := initState f.pk f.ep f.msg f.sig
  let (s1, _, ok1) := runUntil H_test legFuel s0 (addr idxAuth) {}
  let (_, st, ok2) := runUntil H_test legFuel s1 (addr idxFinal) {}
  if ok1 && ok2 then some (st.steps, st.hashes) else none

/-- `authCost_correct` against the interpreter. -/
def checkAuthCost (f : Fixture) : Option String × Nat :=
  match authLeg f with
  | none => (some s!"authcost {f.name}: did not reach the auth/final boundaries", 0)
  | some (steps, hashes) =>
    let predicted := authSteps f.ep.val
    if steps != predicted then
      (some s!"authcost {f.name}: measured {steps} steps, authSteps predicts {predicted}", steps)
    else if hashes != 32 then
      (some s!"authcost {f.name}: {hashes} hashes, expected 32 (one per merkle level)", steps)
    else (none, steps)

/-- The accepting fixtures, with their epoch's population count. -/
def authCostCorpus : List Fixture := corpus.filter (fun f => f.expected)

/-! ## The pinned hash counts

These are equalities, not bounds. `otsHashes` is forced: one encoding hash,
`42` chain-start hashes plus `99 - 42 = 57` further chain steps... in fact the
target sum forces exactly `99` chain hashes for any accepting signature, so
`1 + 99 + 1 = 101`. `xmssHashes` adds the 32 merkle levels. -/

def otsHashesPin : Nat := 101
def xmssHashesPin : Nat := 133

/-- Hashes charged up to `idxAuth` (the semantic OTS cut: after the leaf hash,
    before the first authentication instruction) and in total. -/
def hashSplit (f : Fixture) : Option (Nat × Nat) :=
  let s0 := initState f.pk f.ep f.msg f.sig
  let (s1, st1, ok1) := runUntil H_test legFuel s0 (addr idxAuth) {}
  let (_, st2, stop) := runH H_test verifierFuel s1 st1
  if ok1 && stop == Stop.halted then some (st1.hashes, st2.hashes) else none

def checkHashPin (f : Fixture) : Option String :=
  match hashSplit f with
  | none => some s!"hashpin {f.name}: did not reach the OTS cut, or did not halt"
  | some (ots, tot) =>
    if ots != otsHashesPin then
      some s!"hashpin {f.name}: {ots} OTS hashes, pin is {otsHashesPin}"
    else if tot != xmssHashesPin then
      some s!"hashpin {f.name}: {tot} XMSS hashes, pin is {xmssHashesPin}"
    else none

/-- Steps up to the OTS cut: the quantity the benchmark's first component
    scores. It must be the same for every accepting fixture -- the target sum
    forces the chain work -- or "OTS steps on an accepting path" names no
    single number and the primary score is not well defined. The gate asserts
    it, which is why no held-out corpus is needed. -/
def otsSteps (f : Fixture) : Option Nat :=
  let s0 := initState f.pk f.ep f.msg f.sig
  let (_, st, ok) := runUntil H_test legFuel s0 (addr idxAuth) {}
  if ok then some st.steps else none

end XmssAsm.Tests
