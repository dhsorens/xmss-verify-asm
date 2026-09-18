/-
  XmssAsm

  A formally verified XMSS verifier in RISC-V (RV64IM) assembly, in Lean 4.

  The machine is `riscv-zkvm`'s RV64IM model, reached through `riscv-decomp`'s
  program logic; the specification is leanVM's `XmssSecurity.Scheme`. See
  `README.md` for the stack and the layering rules.

  This root is a LEGACY file (no `module` header), deliberately: `xmss-security`
  is a legacy package and a `module` cannot import a legacy file.
  `XmssAsm.Upstream` is the module-system hub for the machine side, so anything
  naming `XmssSecurity.*` -- including this root -- is legacy, and everything
  else is a `module`.
-/

import XmssAsm.Upstream
import XmssAsm.Spec
import XmssAsm.Machine.Hash
import XmssAsm.Machine.Layout
import XmssAsm.Machine.Cost
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
import XmssAsm.Spec.Decode
import XmssAsm.Regions.Decode
import XmssAsm.Regions.Auth
import XmssAsm.Regions.AuthCost
import XmssAsm.Regions.Final
import XmssAsm.Represent
import XmssAsm.Contract
import XmssAsm.Verify
