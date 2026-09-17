/-
  XmssAsm.Regions.Leaf

  The leaf region: write the leaf tweak into `BUFL`, hash the 704-byte buffer
  `tweak ‖ P ‖ endpoints`, store the digest into `CUR`. LEGACY file.
-/

import XmssAsm.Regions.Common

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- The write set of `leaf`: the `BUFL` tweak, `CUR`, and `OUT`. -/
def WLeaf (a : Word) : Prop := InRange BUFL 16 a ∨ InRange CUR 16 a ∨ InRange OUT 32 a

def LeafPost (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter) (ep : Epoch)
    (e : ChainIndex → Digest) (s : MachineState) : Prop :=
  s.pc = addr idxAuth ∧ s.getReg .x8 = BitVec.ofNat 64 ep.val ∧
  HasDigest s CUR (leafD H P ep e) ∧ Frame WLeaf s0 s

set_option maxRecDepth 4000 in
theorem leaf_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxLeaf) leaf 0) (P : PublicParameter) (ep : Epoch)
    (e : ChainIndex → Digest) (hpc : s.pc = addr idxLeaf) (h8 : s.getReg .x8 = BitVec.ofNat 64 ep.val)
    (hP : HasDigest s BUFL_P P)
    (hE : ∀ j : ChainIndex, HasDigest s (ENDPTS + BitVec.ofNat 64 (16 * j.val)) (e j)) :
    Runs H s (LeafPost H s P ep e) := by
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest] at hP hE
  sym_norm at hpc h8 hP hE
  subst hpc
  sym_code1 hC [leaf]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, -⟩ := hC
  sym_plain_f f0; sym_plain_f f1; sym_sd_f f2; sym_plain_f f3; sym_sd_f f4
  sym_plain_f f5; sym_plain_f f6; sym_plain_f f7; sym_plain_f f8
  sym_hash_in_f f9 (wordsBytes ([tw0 2 0, tw1 ep.val, dLo P, dHi P] ++ digestsWords (List.ofFn e)))
  case hin =>
    rw [hashInputOf_eq _ 88 (by sym_norm) (by sym_norm) (by sym_norm),
      show (88 : Nat) = 4 + 2 * 42 from rfl, readWords_add, readWords_digests _ 42 _ e ?hE']
    case hE' =>
      intro j
      have hj := hE j
      have hj42 : j.val < 42 := j.isLt
      simp only [HasDigest]
      sym_norm
      have t1 : ¬ (67424#64 + BitVec.ofNat 64 (16 * j.val) = 67400#64) := by addr_ne
      have t2 : ¬ (67424#64 + BitVec.ofNat 64 (16 * j.val) = 67392#64) := by addr_ne
      have t3 : ¬ (67424#64 + BitVec.ofNat 64 (16 * j.val) + 8#64 = 67400#64) := by addr_ne
      have t4 : ¬ (67424#64 + BitVec.ofNat 64 (16 * j.val) + 8#64 = 67392#64) := by addr_ne
      simp only [t1, t2, t3, t4, ↓reduceIte]
      exact hj
    simp only [MachineState.readWords_succ, MachineState.readWords_zero]
    sym_norm
    simp only [hP.1, hP.2, h8, tw0_leaf, tw1_machine]
    rfl
  sym_plain_f f10; sym_ld_f f11; sym_ld_f f12; sym_plain_f f13; sym_sd_f f14; sym_sd_f f15
  refine Runs.done ⟨?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm; exact h8
  · simp only [HasDigest]; sym_norm; rw [leafD_eq, dLo_truncateHash, dHi_truncateHash]; exact ⟨rfl, rfl⟩
  · sym_frame_W WLeaf

end XmssAsm
