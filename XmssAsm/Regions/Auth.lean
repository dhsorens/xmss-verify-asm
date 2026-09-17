/-
  XmssAsm.Regions.Auth

  The authentication-path region: 32 levels, each hashing the current node
  with its sibling in the order bit `L` of the epoch dictates, under the
  merkle tweak `(3, L + 1, ep >>> (L + 1))`. LEGACY file.
-/

import XmssAsm.Regions.Common

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-! ## The spec side -/

/-- The root after `L` levels, as a digest. -/
def authD (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch) (sig : Signature)
    (leaf : Digest) (L : Nat) : Digest :=
  evalH H (Concrete.authenticationRoot P ep sig L leaf : OracleComp HashSpec Digest)

theorem authD_zero (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch) (sig : Signature)
    (leaf : Digest) : authD H P ep sig leaf 0 = leaf := rfl

/-- The merkle hash's input as the machine's eight doublewords. -/
theorem merkle_input (P : PublicParameter) (l : MerkleLevel) (n : MerkleNode) (a b : Digest) :
    tweakableHashInput P (.merkle l n) (Concrete.nodePayload a b) =
      wordsBytes [tw0 3 (l.val + 1), tw1 n.val, dLo P, dHi P, dLo a, dHi a, dLo b, dHi b] := by
  rw [tweakableHashInput_eq _ _ _ _ (tweakBytes_merkle l n), nodePayload_eq, ← wordsBytes_append]
  rfl

theorem nodeIndex_val (ep : Epoch) (L : Nat) : (Concrete.nodeIndex ep L).val = ep.val / 2 ^ (L + 1) := rfl

theorem authD_succ_true (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (sig : Signature) (leaf : Digest) (L : Nat) (hL : L < 32) (hb : ep.val.testBit L = true) :
    authD H P ep sig leaf (L + 1) = truncateHash (H (wordsBytes
      [tw0 3 (L + 1), tw1 (ep.val / 2 ^ (L + 1)), dLo P, dHi P,
       dLo (sig.authPath ⟨L, hL⟩), dHi (sig.authPath ⟨L, hL⟩),
       dLo (authD H P ep sig leaf L), dHi (authD H P ep sig leaf L)])) := by
  unfold authD
  rw [evalH_authRoot_succ _ _ _ _ _ _ hL]
  simp only [hb, ite_true]
  exact congrArg (fun i => truncateHash (H i))
    (merkle_input P ⟨L, hL⟩ (Concrete.nodeIndex ep L) (sig.authPath ⟨L, hL⟩) _)

theorem authD_succ_false (H : HashInput → HashOutput) (P : PublicParameter) (ep : Epoch)
    (sig : Signature) (leaf : Digest) (L : Nat) (hL : L < 32) (hb : ep.val.testBit L = false) :
    authD H P ep sig leaf (L + 1) = truncateHash (H (wordsBytes
      [tw0 3 (L + 1), tw1 (ep.val / 2 ^ (L + 1)), dLo P, dHi P,
       dLo (authD H P ep sig leaf L), dHi (authD H P ep sig leaf L),
       dLo (sig.authPath ⟨L, hL⟩), dHi (sig.authPath ⟨L, hL⟩)])) := by
  unfold authD
  rw [evalH_authRoot_succ _ _ _ _ _ _ hL]
  simp only [hb, Bool.false_eq_true, ite_false]
  exact congrArg (fun i => truncateHash (H i))
    (merkle_input P ⟨L, hL⟩ (Concrete.nodeIndex ep L) _ (sig.authPath ⟨L, hL⟩))

/-! ## The machine side -/

theorem bit_test (ep : Epoch) (L : Nat) :
    ((BitVec.ofNat 64 ep.val >>> L) &&& 1#64 = 0#64) ↔ ep.val.testBit L = false := by
  have he : ep.val < 2 ^ 32 := ep.isLt
  rw [BitVec.toNat_eq]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not, Nat.reducePow, Nat.reduceMod]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (a := ep.val) (by omega)]
  omega

theorem tw1_node (ep : Epoch) (L : Nat) :
    BitVec.ofNat 64 ep.val >>> (L + 1) <<< 32 = tw1 (ep.val / 2 ^ (L + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have he : ep.val < 2 ^ 32 := ep.isLt
  simp only [tw1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (a := ep.val) (by omega)]

theorem tw0_merkle (L : Nat) : (BitVec.ofNat 64 L + 1#64) <<< 32 + 768#64 = tw0 3 (L + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [tw0, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem shamt_small (L : Nat) (hL : L < 64) : (BitVec.ofNat 64 L).toNat % 64 = L := by
  simp only [BitVec.toNat_ofNat]; omega

theorem shamt_succ (L : Nat) (hL : L + 1 < 64) : (BitVec.ofNat 64 L + 1#64).toNat % 64 = L + 1 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The write set of the auth region: the `BUFA` tweak, the 32-byte payload, `OUT`. -/
def WAuth (a : Word) : Prop := InRange BUFA 16 a ∨ InRange CUR 32 a ∨ InRange OUT 32 a

theorem not_WAuth_bufaP : ¬ WAuth BUFA_P ∧ ¬ WAuth (BUFA_P + 8) := by
  simp only [WAuth, InRange, not_or, BUFA, CUR, OUT, BUFA_P]; decide

theorem not_WAuth_auth (L : Nat) (hL : L < 32) :
    ¬ WAuth (AUTH + BitVec.ofNat 64 (16 * L)) ∧ ¬ WAuth (AUTH + BitVec.ofNat 64 (16 * L) + 8) := by
  simp only [WAuth, InRange, not_or, BUFA, CUR, OUT, AUTH, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.reduceToNat, Nat.reducePow]
  omega

/-- After `authHash` (pc `idxAuthHash + 23`, the `BNE`): the parent of the payload
    `[p0, p1, p2, p3]` is in `CUR`, the level registers advanced. -/
def AuthHashPost (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter) (ep : Epoch)
    (L : Nat) (p0 p1 p2 p3 : Word) (s : MachineState) : Prop :=
  s.pc = addr (idxAuthHash + 23) ∧ s.getReg .x8 = BitVec.ofNat 64 ep.val ∧
  s.getReg .x25 = BitVec.ofNat 64 (L + 1) ∧ s.getReg .x26 = AUTH + BitVec.ofNat 64 (16 * (L + 1)) ∧
  s.getReg .x6 = 32#64 ∧
  HasDigest s CUR (truncateHash (H (wordsBytes
    [tw0 3 (L + 1), tw1 (ep.val / 2 ^ (L + 1)), dLo P, dHi P, p0, p1, p2, p3]))) ∧
  Frame WAuth s0 s

set_option maxRecDepth 4000 in
theorem authHash_correct (H : HashInput → HashOutput) (s0 s : MachineState)
    (hC : CodeAt s.code (addr idxAuth) auth 0) (P : PublicParameter) (ep : Epoch) (L : Nat)
    (hL : L < 32) (p0 p1 p2 p3 : Word) (hfr0 : Frame WAuth s0 s) (hpc : s.pc = addr idxAuthHash)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 ep.val) (h25 : s.getReg .x25 = BitVec.ofNat 64 L)
    (h26 : s.getReg .x26 = AUTH + BitVec.ofNat 64 (16 * L)) (hP : HasDigest s BUFA_P P)
    (hp : s.getMem CUR = p0 ∧ s.getMem (CUR + 8) = p1 ∧ s.getMem (CUR + 16) = p2 ∧ s.getMem (CUR + 24) = p3) :
    Runs H s (AuthHashPost H s0 P ep L p0 p1 p2 p3) := by
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest] at hP
  sym_norm at hpc h8 h25 h26 hP hp
  subst hpc
  sym_code hC [auth, authPre, authLoop] [authBody, authSelect, authHash]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f17, f18, f19, f20, f21, f22, f23, f24,
    f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, -⟩ := hC
  sym_plain_f f17; sym_plain_f f18; sym_plain_f f19; sym_plain_f f20; sym_sd_f f21
  sym_plain_f f22; sym_plain_f f23; sym_plain_f f24; sym_sd_f f25
  sym_plain_f f26; sym_plain_f f27; sym_plain_f f28; sym_plain_f f29
  sym_hash_in_f f30 (wordsBytes [tw0 3 (L + 1), tw1 (ep.val / 2 ^ (L + 1)), dLo P, dHi P, p0, p1, p2, p3])
  case hin =>
    rw [hashInputOf_eq _ 8 (by sym_norm) (by sym_norm) (by sym_norm)]
    simp only [MachineState.readWords_succ, MachineState.readWords_zero]
    sym_norm
    simp only [h25, h8, shamt_succ L (by omega), tw0_merkle, tw1_node, hP.1, hP.2, hp.1, hp.2.1, hp.2.2.1,
      hp.2.2.2]
  sym_plain_f f31; sym_ld_f f32; sym_ld_f f33; sym_plain_f f34; sym_sd_f f35; sym_sd_f f36
  sym_plain_f f37; sym_plain_f f38; sym_plain_f f39
  refine Runs.done ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm; exact h8
  · sym_norm; rw [h25, ofNat_succ]
  · sym_norm; rw [h26]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · sym_norm
  · simp only [HasDigest]; sym_norm; rw [dLo_truncateHash, dHi_truncateHash]; exact ⟨rfl, rfl⟩
  · exact Frame.trans hfr0 (by sym_frame_W WAuth)

/-! ## The loop -/

/-- The invariant at the loop head after `L` levels (at `idxFinal` once all 32 are done). -/
def AuthInv (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter) (ep : Epoch)
    (sig : Signature) (leaf : Digest) (L : Nat) (s : MachineState) : Prop :=
  s.code = s0.code ∧ s.pc = (if L < 32 then addr idxAuthLoop else addr idxFinal) ∧
  s.getReg .x8 = BitVec.ofNat 64 ep.val ∧ s.getReg .x25 = BitVec.ofNat 64 L ∧
  s.getReg .x26 = AUTH + BitVec.ofNat 64 (16 * L) ∧
  HasDigest s CUR (authD H P ep sig leaf L) ∧ Frame WAuth s0 s

def AuthPost (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter) (ep : Epoch)
    (sig : Signature) (leaf : Digest) (s : MachineState) : Prop :=
  s.pc = addr idxFinal ∧ HasDigest s CUR (authD H P ep sig leaf 32) ∧ Frame WAuth s0 s

/-- From the `BNE` after `authHash` to the invariant at `L + 1`. -/
theorem auth_tail (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxAuth) auth 0) (P : PublicParameter) (ep : Epoch) (sig : Signature)
    (leaf : Digest) (L : Nat) (hL : L < 32) (p0 p1 p2 p3 : Word)
    (heq : truncateHash (H (wordsBytes [tw0 3 (L + 1), tw1 (ep.val / 2 ^ (L + 1)), dLo P, dHi P, p0, p1, p2, p3]))
      = authD H P ep sig leaf (L + 1))
    (s : MachineState) (hpost : AuthHashPost H s0 P ep L p0 p1 p2 p3 s) :
    Runs H s (AuthInv H s0 P ep sig leaf (L + 1)) := by
  obtain ⟨hpc, h8, h25, h26, h6, hcur, hfr⟩ := hpost
  have hcode : s.code = s0.code := hfr.code
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  rw [heq] at hcur
  simp only [HasDigest] at hcur
  sym_norm at hpc h8 h25 h26 h6 hcur hcode
  subst hpc
  rw [← hcode] at hC
  sym_code hC [auth, authPre, authLoop] [authBody, authSelect, authHash]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, f40, -⟩ := hC
  sym_plain_f f40
  simp only [h25, h6]
  rcases Nat.lt_or_ge (L + 1) 32 with hlt | hge
  · have hne : ¬ (BitVec.ofNat 64 (L + 1) = 32#64) := by
      intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    simp only [hne, not_false_eq_true, ↓reduceIte]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_norm; rw [if_pos hlt]
    · sym_norm; exact h8
    · sym_norm; exact h25
    · sym_norm; exact h26
    · simp only [HasDigest]; sym_norm; exact hcur
    · exact Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · have heq' : BitVec.ofNat 64 (L + 1) = 32#64 := by rw [show L + 1 = 32 by omega]
    simp only [heq', not_true_eq_false, ↓reduceIte]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_norm; rw [if_neg (by omega)]
    · sym_norm; exact h8
    · sym_norm; exact h25
    · sym_norm; exact h26
    · simp only [HasDigest]; sym_norm; exact hcur
    · exact Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

set_option maxRecDepth 4000 in
theorem auth_body (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxAuth) auth 0) (P : PublicParameter) (ep : Epoch) (sig : Signature)
    (leaf : Digest) (hP0 : HasDigest s0 BUFA_P P)
    (hA0 : ∀ l : MerkleLevel, HasDigest s0 (AUTH + BitVec.ofNat 64 (16 * l.val)) (sig.authPath l))
    (L : Nat) (hL : L < 32) (s : MachineState) (hI : AuthInv H s0 P ep sig leaf L s) :
    Runs H s (AuthInv H s0 P ep sig leaf (L + 1)) := by
  obtain ⟨hcode, hpc, h8, h25, h26, hcur, hfr⟩ := hI
  have hP : HasDigest s BUFA_P P :=
    ⟨(hfr.mem _ not_WAuth_bufaP.1).trans hP0.1, (hfr.mem _ not_WAuth_bufaP.2).trans hP0.2⟩
  have hsib : HasDigest s (AUTH + BitVec.ofNat 64 (16 * L)) (sig.authPath ⟨L, hL⟩) :=
    ⟨(hfr.mem _ (not_WAuth_auth L hL).1).trans (hA0 ⟨L, hL⟩).1,
     (hfr.mem _ (not_WAuth_auth L hL).2).trans (hA0 ⟨L, hL⟩).2⟩
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  rw [if_pos hL] at hpc
  simp only [HasDigest] at hP hsib hcur
  sym_norm at hcode hpc h8 h25 h26 hP hsib hcur
  subst hpc
  have hCc : CodeAt C (addr idxAuth) auth 0 := by rw [hcode]; exact hC
  have hC' := hCc
  sym_code hC' [auth, authPre, authLoop] [authBody, authSelect, authHash]
  obtain ⟨-, -, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, -⟩ := hC'
  sym_ld_f_with f2 (by sym_norm; rw [h26]; sym_valid_off)
  sym_ld_f_with f3 (by sym_norm; rw [h26]; sym_valid_off)
  sym_plain_f f4; sym_ld_f f5; sym_ld_f f6
  sym_plain_f f7; sym_plain_f f8; sym_plain_f f9
  have hb : (R .x8 >>> ((R .x25).toNat % 64) &&& 1#64 = 0#64) ↔ ep.val.testBit L = false := by
    rw [h8, h25, shamt_small L (by omega)]; exact bit_test ep L
  have e1 : M (R .x26) = dLo (sig.authPath ⟨L, hL⟩) := by rw [h26]; exact hsib.1
  have e2 : M (R .x26 + 8#64) = dHi (sig.authPath ⟨L, hL⟩) := by rw [h26]; exact hsib.2
  by_cases ht : ep.val.testBit L = false
  · rw [if_pos (hb.mpr ht)]
    sym_sd_f f15; sym_sd_f f16
    refine Runs.bind (authHash_correct H _ _ hCc P ep L hL (dLo (authD H P ep sig leaf L))
      (dHi (authD H P ep sig leaf L)) (dLo (sig.authPath ⟨L, hL⟩)) (dHi (sig.authPath ⟨L, hL⟩))
      (Frame.trans hfr (by sym_frame_W WAuth)) (by sym_norm) (by sym_norm; exact h8) (by sym_norm; exact h25)
      (by sym_norm; exact h26) (by simp only [HasDigest]; sym_norm; exact hP)
      ⟨by sym_norm; exact hcur.1, by sym_norm; exact hcur.2, by sym_norm; exact e1, by sym_norm; exact e2⟩)
      (fun s2 hpost => auth_tail H _ hC P ep sig leaf L hL _ _ _ _ (authD_succ_false H P ep sig leaf L hL ht).symm
        s2 hpost)
  · have ht' : ep.val.testBit L = true := by simpa using ht
    rw [if_neg (fun h => ht (hb.mp h))]
    sym_sd_f f10; sym_sd_f f11; sym_sd_f f12; sym_sd_f f13; sym_plain_f f14
    refine Runs.bind (authHash_correct H _ _ hCc P ep L hL (dLo (sig.authPath ⟨L, hL⟩))
      (dHi (sig.authPath ⟨L, hL⟩)) (dLo (authD H P ep sig leaf L)) (dHi (authD H P ep sig leaf L))
      (Frame.trans hfr (by sym_frame_W WAuth)) (by sym_norm) (by sym_norm; exact h8) (by sym_norm; exact h25)
      (by sym_norm; exact h26) (by simp only [HasDigest]; sym_norm; exact hP)
      ⟨by sym_norm; exact e1, by sym_norm; exact e2, by sym_norm; exact hcur.1, by sym_norm; exact hcur.2⟩)
      (fun s2 hpost => auth_tail H _ hC P ep sig leaf L hL _ _ _ _ (authD_succ_true H P ep sig leaf L hL ht').symm
        s2 hpost)

theorem auth_entry (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxAuth) auth 0) (P : PublicParameter) (ep : Epoch) (sig : Signature)
    (leaf : Digest) (hpc : s.pc = addr idxAuth) (h8 : s.getReg .x8 = BitVec.ofNat 64 ep.val)
    (hleaf : HasDigest s CUR leaf) : Runs H s (AuthInv H s P ep sig leaf 0) := by
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest] at hleaf
  sym_norm at hpc h8 hleaf
  subst hpc
  sym_code hC [auth, authPre, authLoop] [authBody, authSelect, authHash]
  obtain ⟨f0, f1, -⟩ := hC
  sym_plain_f f0; sym_plain_f f1
  refine Runs.done ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm; exact h8
  · sym_norm
  · sym_norm
  · simp only [HasDigest, authD_zero]; sym_norm; exact hleaf
  · exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩

/-- The authentication-path region: the root after 32 levels is in `CUR`. -/
theorem auth_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxAuth) auth 0) (P : PublicParameter) (ep : Epoch) (sig : Signature)
    (leaf : Digest) (hpc : s.pc = addr idxAuth) (h8 : s.getReg .x8 = BitVec.ofNat 64 ep.val)
    (hleaf : HasDigest s CUR leaf) (hP0 : HasDigest s BUFA_P P)
    (hA0 : ∀ l : MerkleLevel, HasDigest s (AUTH + BitVec.ofNat 64 (16 * l.val)) (sig.authPath l)) :
    Runs H s (AuthPost H s P ep sig leaf) :=
  Runs.bind (auth_entry H s hC P ep sig leaf hpc h8 hleaf) fun s1 h1 =>
    Runs.mono (Runs.loop 32 (fun L s' hL hI => auth_body H s hC P ep sig leaf hP0 hA0 L hL s' hI) s1 h1)
      fun s' hI => ⟨hI.2.1.trans (if_neg (by decide)), hI.2.2.2.2.2.1, hI.2.2.2.2.2.2⟩

end XmssAsm
