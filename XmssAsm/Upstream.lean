/-
  XmssAsm.Upstream

  The machine side, re-exported once: `riscv-zkvm`'s RV64IM model and program
  logic, reached through `Decomp.Upstream` (its two legacy aggregators cannot
  be imported from a `module`), and `riscv-decomp`'s decompilation layer.
  Every `module` file here reaches those names through
  `public import XmssAsm.Upstream`.

  `Refine` (lean-refine) is NOT here: that package is legacy, so it can only be
  imported from a legacy file. `XmssAsm.Smoke` shows the pattern.
-/

module

public import Decomp
