/-
  XmssAsm.Spec.Eval

  Evaluating the upstream verifier under a fixed answer function.

  `XmssSecurity.Concrete.verify` lives in any monad with a `HashSpec` oracle.
  The machine has one concrete hash `H : HashInput → HashOutput`, so the
  specification it is compared against is `Concrete.verify` run in
  `OracleComp HashSpec` with every query answered by `H` --
  VCVio's `evalWithAnswerFn H`, the same idiom `Scheme.lean` itself uses for
  `precomputedSecretKey`. These lemmas unfold the spec's monadic definitions
  under that evaluation into the pure equations the region contracts are
  stated with. Nothing here introduces a second verifier: every right-hand
  side is the spec's own function, evaluated.

  Legacy file: it imports `XmssSecurity.Scheme`.
-/

import XmssSecurity.Scheme

namespace XmssAsm

open XmssSecurity OracleComp

/-- Shorthand: a spec computation evaluated with every query answered by `H`. -/
abbrev evalH (H : HashInput → HashOutput) {α : Type} (oa : OracleComp HashSpec α) : α :=
  evalWithAnswerFn H oa

theorem evalH_query (H : HashInput → HashOutput) (t : HashInput) :
    evalH H (liftM (OracleSpec.query (spec := HashSpec) t) : OracleComp HashSpec HashOutput) = H t :=
  simulateQ_spec_query (spec := HashSpec) (r := Id) (impl := (H : QueryImpl HashSpec Id)) t

@[simp] theorem evalH_pure (H : HashInput → HashOutput) {α : Type} (a : α) :
    evalH H (pure a : OracleComp HashSpec α) = a := rfl

@[simp] theorem evalH_bind (H : HashInput → HashOutput) {α β : Type}
    (oa : OracleComp HashSpec α) (ob : α → OracleComp HashSpec β) :
    evalH H (oa >>= ob) = evalH H (ob (evalH H oa)) :=
  evalWithAnswerFn_bind H oa ob

/-- `Th(P, tw, M)` evaluated: the truncated hash of the tweaked input. -/
theorem evalH_tweakableHash (H : HashInput → HashOutput) (P : PublicParameter)
    (dom : HashDomain) (payload : HashInput) :
    evalH H (Concrete.tweakableHash P dom payload : OracleComp HashSpec Digest)
      = truncateHash (H (tweakableHashInput P dom payload)) := by
  simp [evalH, Concrete.tweakableHash, Concrete.oracleHash, evalH_query]

theorem evalH_chainWalk_zero (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (i : ChainIndex) (pos : Nat) (v : Digest) :
    evalH H (Concrete.chainWalk P ep i pos 0 v : OracleComp HashSpec Digest) = v := rfl

/-- One more chain step, at position `pos + steps`. -/
theorem evalH_chainWalk_succ (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (i : ChainIndex) (pos steps : Nat) (v : Digest) (h : pos + steps < chainLength - 1) :
    evalH H (Concrete.chainWalk P ep i pos (steps + 1) v : OracleComp HashSpec Digest)
      = truncateHash (H (tweakableHashInput P (.chain ep i ⟨pos + steps, h⟩)
          (bytesLE 16 (evalH H (Concrete.chainWalk P ep i pos steps v : OracleComp HashSpec Digest))))) := by
  simp only [evalH, Concrete.chainWalk, evalWithAnswerFn_bind, h, dite_true, Concrete.chainHash,
    evalH_tweakableHash]
  rfl

theorem evalH_recoverChain (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (i : ChainIndex) (x : Digit) (v : Digest) :
    evalH H (Concrete.recoverChain P ep i x v : OracleComp HashSpec Digest)
      = evalH H (Concrete.chainWalk P ep i x.val (chainLength - 1 - x.val) v : OracleComp HashSpec Digest) :=
  rfl

/-- `sequenceFin` evaluated pointwise. -/
theorem evalH_sequenceFin (H : HashInput → HashOutput) {α : Type} :
    ∀ (n : Nat) (f : Fin n → OracleComp HashSpec α),
      evalH H (Concrete.sequenceFin f) = fun i => evalH H (f i) := by
  intro n
  induction n with
  | zero => intro f; funext i; exact i.elim0
  | succ n ih =>
    intro f
    simp only [evalH, Concrete.sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp

theorem evalH_recoverEndpoints (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (enc : Encoding) (sig : Signature) :
    evalH H (Concrete.recoverEndpoints P ep enc sig : OracleComp HashSpec (ChainIndex → Digest))
      = fun i => evalH H (Concrete.recoverChain P ep i (enc i) (sig.chainValue i) : OracleComp HashSpec Digest) := by
  simp only [Concrete.recoverEndpoints, evalH_sequenceFin]

theorem evalH_leafHash (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (endpoints : ChainIndex → Digest) :
    evalH H (Concrete.leafHash P ep endpoints : OracleComp HashSpec Digest)
      = truncateHash (H (tweakableHashInput P (.leaf ep) (Concrete.leafPayload endpoints))) :=
  evalH_tweakableHash H P _ _

theorem evalH_authRoot_zero (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (sig : Signature) (leaf : Digest) :
    evalH H (Concrete.authenticationRoot P ep sig 0 leaf : OracleComp HashSpec Digest) = leaf := rfl

/-- One more authentication level. -/
theorem evalH_authRoot_succ (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (sig : Signature) (leaf : Digest) (l : Nat) (hl : l < treeHeight) :
    evalH H (Concrete.authenticationRoot P ep sig (l + 1) leaf : OracleComp HashSpec Digest)
      = (let cur := evalH H (Concrete.authenticationRoot P ep sig l leaf : OracleComp HashSpec Digest)
         let sib := sig.authPath ⟨l, hl⟩
         truncateHash (H (tweakableHashInput P (.merkle ⟨l, hl⟩ (Concrete.nodeIndex ep l))
           (if ep.val.testBit l then Concrete.nodePayload sib cur else Concrete.nodePayload cur sib)))) := by
  simp only [evalH, Concrete.authenticationRoot, evalWithAnswerFn_bind, Concrete.authenticationNodeHash,
    hl, dite_true, Concrete.signaturePath, Concrete.nodeHash]
  split
  · simp [evalH_tweakableHash]
  · simp [evalH_tweakableHash]

/-- `Ver(pk, ep, m, σ)` evaluated: the pure shape the machine implements. -/
theorem evalH_verify (H : HashInput → HashOutput) (pk : PublicKey) (ep : Epoch)
    (msg : Message) (sig : Signature) :
    evalH H (Concrete.verify pk ep msg sig : OracleComp HashSpec Bool) =
      match TargetSum.decodeDigest (truncateHash (H (tweakableHashInput pk.parameter (.encoding ep)
          (Concrete.encodingPayload msg sig.randomness)))) with
      | none => false
      | some enc =>
        let endpoints := fun i => evalH H
          (Concrete.recoverChain pk.parameter ep i (enc i) (sig.chainValue i) : OracleComp HashSpec Digest)
        let leaf := truncateHash (H (tweakableHashInput pk.parameter (.leaf ep)
          (Concrete.leafPayload endpoints)))
        decide (evalH H (Concrete.authenticationRoot pk.parameter ep sig treeHeight leaf :
          OracleComp HashSpec Digest) = pk.root) := by
  simp only [evalH, Concrete.verify, Concrete.encodingHash, evalWithAnswerFn_bind, evalH_tweakableHash]
  cases TargetSum.decodeDigest _ with
  | none => simp
  | some enc =>
    simp only [evalWithAnswerFn_bind, Concrete.recoverEndpoints, evalH_sequenceFin,
      Concrete.leafHash, evalH_tweakableHash]
    unfold Concrete.verifyAfterLeaf
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-! ## An executable form of the evaluated verifier

`Concrete.verify` evaluated under `H` is what the correctness theorem is
stated against. Evaluating that term directly is impractical: the spec's
`sequenceFin` returns a nest of `Fin.cases`, whose strict evaluation is
exponential in the index. `specVerify` is the right-hand side of
`evalH_verify` -- the same spec functions, evaluated pointwise -- and
`specVerify_eq` is the machine-checked fact that it is the same Boolean. The
differential tests compute their expected results with `specVerify`; the
theorem never mentions it. -/

/-- `Concrete.verify pk ep msg sig` under `H`, in evaluable form. -/
def specVerify (H : HashInput → HashOutput) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) : Bool :=
  match TargetSum.decodeDigest (truncateHash (H (tweakableHashInput pk.parameter (.encoding ep)
      (Concrete.encodingPayload msg sig.randomness)))) with
  | none => false
  | some enc =>
    let endpoints := fun i => evalH H
      (Concrete.recoverChain pk.parameter ep i (enc i) (sig.chainValue i) : OracleComp HashSpec Digest)
    let leaf := truncateHash (H (tweakableHashInput pk.parameter (.leaf ep)
      (Concrete.leafPayload endpoints)))
    decide (evalH H (Concrete.authenticationRoot pk.parameter ep sig treeHeight leaf :
      OracleComp HashSpec Digest) = pk.root)

theorem specVerify_eq (H : HashInput → HashOutput) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) :
    specVerify H pk ep msg sig = evalH H (Concrete.verify pk ep msg sig : OracleComp HashSpec Bool) :=
  (evalH_verify H pk ep msg sig).symm

end XmssAsm
