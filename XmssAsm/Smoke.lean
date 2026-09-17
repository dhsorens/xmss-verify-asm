/-
  XmssAsm.Smoke

  A wiring check, not a result: this file exists so that `lake build` fails if
  any of the three machine-side dependencies is unreachable, and so that the
  vocabulary the project will be written in is visible in one place.

  Legacy file (no `module`): it imports `Refine`, which is a legacy package.

  Delete it once a real module imports the same things.
-/

import XmssAsm.Upstream
import Refine

namespace XmssAsm

open RiscvZkvm.Rv64

/-- A two-instruction program, to confirm `Program` and the macro-assembler
    constructors resolve. `x10 := 0; x11 := x10 + 1`. -/
def smokeProgram : Program :=
  ADDI .x10 .x0 0 ;; ADDI .x11 .x10 1

/-- The machine model, the decompilation judgements and the refinement monad
    are all in scope. Silent `example`s rather than `#check`s so a clean build
    prints nothing. -/
example : Program := smokeProgram
example := @Decomp.cpsTotal
example := @Refine.Nres
example := @Refine.spec

end XmssAsm
