/-
  XmssAsm

  A formally verified XMSS verifier in RISC-V (RV64IM) assembly, in Lean 4.

  The machine is `riscv-zkvm`'s RV64IM model; the decompilation layer is
  `riscv-decomp`; the refinement calculus is `lean-refine`; the specification
  is leanVM's `XmssSecurity.Scheme`. See `README.md` for the stack and
  `PLAN.md` for the work queue.

  This root is a LEGACY file (no `module` header), deliberately. Two of the
  four dependencies -- `lean-refine` and `xmss-security` -- are legacy
  packages, and a `module` cannot import a legacy file. `XmssAsm.Upstream` is
  the module-system hub for the machine side (`riscv-zkvm` via `riscv-decomp`);
  anything that names `Refine.*` or `XmssSecurity.*` is a legacy file like this
  one. See `PLAN.md` ("module system") for what it would take to lift this.
-/

import XmssAsm.Upstream
import XmssAsm.Smoke
import XmssAsm.Spec
import XmssAsm.Machine.Hash
import XmssAsm.Machine.Layout
import XmssAsm.Machine.Sym
import XmssAsm.Machine.Eval
import XmssAsm.Program.Verifier
import XmssAsm.Spec.Eval
import XmssAsm.Spec.Bytes
import XmssAsm.Regions.Common
import XmssAsm.Regions.Chain
import XmssAsm.Regions.Init
import XmssAsm.Regions.Chains
import XmssAsm.Regions.Leaf
import XmssAsm.Represent
import XmssAsm.Contract
