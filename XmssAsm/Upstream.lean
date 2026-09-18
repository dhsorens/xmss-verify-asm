/-
  XmssAsm.Upstream

  The machine side, re-exported once: `riscv-zkvm`'s RV64IM model and program
  logic, reached through `Decomp.Upstream` (its two legacy aggregators cannot
  be imported from a `module`), and `riscv-decomp`'s decompilation layer.
  Every `module` file here reaches those names through
  `public import XmssAsm.Upstream`.

  The specification is deliberately not re-exported: `xmss-security` is a
  legacy package, so a file naming `XmssSecurity.*` cannot be a `module` and
  imports the spec directly instead.
-/

module

public import Decomp
