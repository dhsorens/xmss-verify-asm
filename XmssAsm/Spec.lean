/-
  XmssAsm.Spec

  The specification this project proves an implementation against: leanVM's
  `XmssSecurity.Scheme`, imported verbatim from the upstream package (pinned in
  `lakefile.toml`). `xmss_verify_correct` is stated in terms of
  `XmssSecurity.Concrete.verify`.

  This file defines nothing. It is a rename tripwire: the `example`s name every
  upstream constant the proof depends on, so an upstream rename or signature
  change fails here, with a one-line error, instead of surfacing as a broken
  region proof somewhere in `XmssAsm.Regions`.

  LEGACY file, deliberately: `XmssSecurity.Scheme` is not a Lean `module`, and
  a `module` cannot import a legacy file. Everything that names
  `XmssSecurity.*` is legacy for the same reason, up to and including
  `XmssAsm.Verify`.
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
    `xmss_verify_correct` instantiates this shape at an arbitrary
    `H : HashInput → HashOutput`, so it holds for every choice at once. -/
example : PublicKey → Epoch → Message → Signature →
    OracleComp HashSpec Bool :=
  Concrete.verify

end XmssAsm
