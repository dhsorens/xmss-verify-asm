/-
  XmssAsm.Spec

  The specification this project proves an implementation against: leanVM's
  `XmssSecurity.Scheme`, imported verbatim from the upstream package (pinned in
  `lakefile.toml`). The theorem to hit is stated in terms of
  `XmssSecurity.Concrete.verify`.

  This is a LEGACY file, deliberately: `XmssSecurity.Scheme` is not a Lean
  `module`, and a `module` cannot import a legacy file. The eventual bridging
  theorem, which names both `Concrete.verify` and a `Decomp.cpsTotal`, will
  have to live in a legacy file too until the upstream spec adopts the module
  system. See `PLAN.md`.

  Nothing is defined here yet. The `example`s pin the names the bridge will
  use, so an upstream rename fails this build rather than a later proof.
-/

import XmssSecurity.Scheme

namespace XmssAsm

open XmssSecurity

example := @Concrete.verify
example := @Concrete.recoverEndpoints
example := @Concrete.authenticationRoot
example := @TargetSum.decodeDigest
example := @tweakableHashInput

/-- The verifier is stated over any monad with a hash oracle. An implementation
    fixes the oracle to a concrete hash; leanVM's Rust fixes it to BLAKE2s-256.
    This is the shape the bridge will instantiate. -/
example : PublicKey → Epoch → Message → Signature →
    OracleComp HashSpec Bool :=
  Concrete.verify

end XmssAsm
