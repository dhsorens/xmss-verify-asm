/-
  XmssAsmTests.Diff

  The differential harness: run the RV verifier under `stepH H_test` from
  `initState`, compare `a0` with `Concrete.verify` evaluated under `H_test`,
  and report the cycle statistics.
-/

import XmssAsmTests.Fixtures
import XmssAsm.Contract

namespace XmssAsm.Tests

open RiscvZkvm.Rv64 XmssSecurity

structure RunResult where
  halted : Bool
  a0 : Word
  stats : Stats
  deriving Repr

/-- Run a verifier build (`code`) on a fixture. -/
def runFixtureWith (code : CodeMem) (f : Fixture) : RunResult :=
  let s := { initState f.pk f.ep f.msg f.sig with code := code }
  let (s', st, stop) := runH H_test verifierFuel s {}
  ⟨stop == .halted, s'.getReg .x10, st⟩

/-- Run the artifact on a fixture. -/
def runFixture (f : Fixture) : RunResult := runFixtureWith verifierCode f

/-- One end-to-end check of a verifier build. Returns an error message on disagreement. -/
def checkFixtureWith (code : CodeMem) (f : Fixture) : Option String × RunResult :=
  let r := runFixtureWith code f
  let expected := f.expected
  let ok := r.halted && r.a0 == resultWord expected
  (if ok then none else
    some s!"{f.name}: machine halted={r.halted} a0={r.a0.toNat}, spec={expected}", r)

def checkFixture (f : Fixture) : Option String × RunResult := checkFixtureWith verifierCode f

end XmssAsm.Tests
