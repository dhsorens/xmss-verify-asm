/-
  XmssAsm.Regions.Common

  Bridging facts shared by the region proofs: signed compares on small
  naturals, the machine's tweak arithmetic against `tw0`/`tw1`, and the
  hash-call input of a chain step. This is a LEGACY file: it names
  `XmssSecurity.*` through `XmssAsm.Spec.Bytes`.
-/

import XmssAsm.Machine.Sym
import XmssAsm.Spec.Bytes
import XmssAsm.Spec.Eval

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-! ## Arithmetic bridges -/

/-- `BGE`/`BLT` on small non-negative values is the natural-number order. -/
theorem slt_ofNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a).slt (BitVec.ofNat 64 b) = decide (a < b) := by
  have h1 : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_msb]
    · simp [BitVec.toNat_ofNat]; omega
    · rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]; omega
  have h2 : (BitVec.ofNat 64 b).toInt = b := by
    rw [BitVec.toInt_eq_toNat_of_msb]
    · simp [BitVec.toNat_ofNat]; omega
    · rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]; omega
  simp only [BitVec.slt, h1, h2]
  by_cases h : a < b <;> simp [h]

/-- The machine's chain tweak word `((8 i + pos) <<< 32) + 0x100` is `tw0 1 (8 i + pos)`. -/
theorem tw0_machine (p q : Nat) :
    (BitVec.ofNat 64 p + BitVec.ofNat 64 q) <<< 32 + 256#64 = tw0 1 (p + q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [tw0, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

/-- The same tweak word with the position already summed (implementation B). -/
theorem tw0_machine' (p : Nat) : BitVec.ofNat 64 p <<< 32 + 256#64 = tw0 1 p := by
  apply BitVec.eq_of_toNat_eq
  simp only [tw0, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

/-- The machine's epoch tweak word `ep <<< 32` is `tw1 ep`. -/
theorem tw1_machine (e : Nat) : BitVec.ofNat 64 e <<< 32 = tw1 e := by
  apply BitVec.eq_of_toNat_eq
  simp only [tw1, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

theorem ofNat_add_one (a b : Nat) :
    BitVec.ofNat 64 (a + b) + 1#64 = BitVec.ofNat 64 (a + (b + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Spec values as digests

`evalH` is polymorphic in the result type; a `Digest` computed by it is
elaborated against `BitVec 128` in machine statements, which breaks
syntactic rewriting with the `evalH_*` lemmas. These wrappers fix the type. -/

/-- The chain walked `k` steps from `pos`, as a digest. -/
def walkD (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch) (ci : ChainIndex)
    (pos k : Nat) (v : Digest) : Digest :=
  evalH H (Concrete.chainWalk P ep ci pos k v : OracleComp HashSpec Digest)

/-- `recoverChain` evaluated, as a digest. -/
def recoverD (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch) (ci : ChainIndex)
    (x : Digit) (v : Digest) : Digest :=
  evalH H (Concrete.recoverChain P ep ci x v : OracleComp HashSpec Digest)

theorem walkD_zero (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch) (ci : ChainIndex)
    (pos : Nat) (v : Digest) : walkD H P ep ci pos 0 v = v := rfl

theorem recoverD_eq (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch) (ci : ChainIndex)
    (x : Digit) (v : Digest) : recoverD H P ep ci x v = walkD H P ep ci x.val (7 - x.val) v := rfl

/-! ## Hash-call inputs -/

/-- The chain hash's input as the six doublewords the machine lays out in `BUFA`. -/
theorem chain_input (P : PublicParameter) (ep : Epoch) (ci : ChainIndex) (pos : ChainStep)
    (cur : Digest) :
    tweakableHashInput P (.chain ep ci pos) (bytesLE 16 cur) =
      wordsBytes [tw0 1 (8 * ci.val + pos.val), tw1 ep.val, dLo P, dHi P, dLo cur, dHi cur] := by
  rw [tweakableHashInput_eq _ _ _ _ (tweakBytes_chain ep ci pos), bytesLE_digest, ← wordsBytes_append]
  rfl

/-- One chain step: the machine's six-word hash input, truncated. -/
theorem walkD_succ (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch) (ci : ChainIndex)
    (pos k : Nat) (v : Digest) (h : pos + k < 7) :
    walkD H P ep ci pos (k + 1) v =
      truncateHash (H (wordsBytes [tw0 1 (8 * ci.val + (pos + k)), tw1 ep.val, dLo P, dHi P,
        dLo (walkD H P ep ci pos k v), dHi (walkD H P ep ci pos k v)])) := by
  have h' : pos + k < chainLength - 1 := h
  unfold walkD
  rw [evalH_chainWalk_succ _ _ _ _ _ _ _ h']
  exact congrArg (fun i => truncateHash (H i))
    (chain_input P ep ci ⟨pos + k, h'⟩ (walkD H P ep ci pos k v))

end XmssAsm
