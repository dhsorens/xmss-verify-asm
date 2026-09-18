/-
  XmssAsm.Machine.Eval

  The deterministic evaluator and cycle counter.

  It runs `stepH H` -- the very same transition function the correctness
  theorem is stated over -- on the very same `verifier` program value. That is
  deliberate and it is the whole design: the evaluator takes no program
  parameter, so it cannot be pointed at a candidate the theorem is not about,
  and a measured number and a proved number always describe one artifact.

  ## Cost model

      ordinary executed RV instruction = 1 virtual cycle
      abstract hash call (the HASH_ID ECALL) = `hashCost` virtual cycles

  `hashCost` is the one configurable parameter; `defaultHashCost = 1`. Branches,
  memory operations and the final `HALT` ecall are ordinary instructions. The
  halting `ECALL` itself is not executed (the machine stops at it), so it is
  not counted. The reported score for a given input is deterministic.
-/

module

public import XmssAsm.Machine.Hash
public import XmssAsm.Program.Verifier

@[expose] public section

namespace XmssAsm

open RiscvZkvm.Rv64

/-- Execution statistics. `steps` counts every executed instruction including
    hash calls; `hashes` counts the hash calls among them. -/
structure Stats where
  steps : Nat := 0
  hashes : Nat := 0
  deriving Repr, DecidableEq

def Stats.ordinary (st : Stats) : Nat := st.steps - st.hashes

/-- Total synthetic cost under a given hash cost. -/
def Stats.cost (st : Stats) (hashCost : Nat) : Nat := st.ordinary + st.hashes * hashCost

-- adjustable hash cost parameter
def defaultHashCost : Nat := 1

/-- Why a run stopped. -/
inductive Stop where
  /-- At an `ECALL` with `x5 = 0`: the program halted. -/
  | halted
  /-- `stepH` returned `none` elsewhere: a trap. -/
  | trapped
  /-- Fuel exhausted. -/
  | fuelOut
  deriving Repr, DecidableEq

def isHalted (s : MachineState) : Bool :=
  s.code s.pc == some .ECALL && s.getReg .x5 == 0

def isHashCall (s : MachineState) : Bool :=
  s.code s.pc == some .ECALL && s.getReg .x5 == HASH_ID

/-- Run `stepH H` for at most `fuel` steps. -/
def runH (H : List UInt8 → BitVec 256) : Nat → MachineState → Stats → MachineState × Stats × Stop
  | 0, s, st => (s, st, .fuelOut)
  | fuel + 1, s, st =>
    match stepH H s with
    | none => (s, st, if isHalted s then .halted else .trapped)
    | some s' =>
      runH H fuel s' { steps := st.steps + 1, hashes := st.hashes + (if isHashCall s then 1 else 0) }

/-- Fuel that comfortably exceeds any run of the verifier (about 4,500 steps). -/
def verifierFuel : Nat := 100000

/-- The initial machine state: zero registers and memory, the verifier loaded
    at `CODE_BASE`, pc at `CODE_BASE`. The inputs are written on top by
    `XmssAsm.initState`. -/
def blankState : MachineState :=
  { regs := fun _ => 0, mem := fun _ => 0, code := verifierCode, pc := CODE_BASE }

/-- Static instruction count of the artifact. -/
def staticInstructionCount : Nat := verifier.length

end XmssAsm
