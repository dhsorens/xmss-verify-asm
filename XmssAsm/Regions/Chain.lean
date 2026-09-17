/-
  XmssAsm.Regions.Chain

  The chain-walk region. From `x14 = x`, `x16 = 8 i`, `x8 = ep`, `CUR = v`,
  `BUFA_P = P`, execution reaches the instruction after the region with
  `CUR = recoverChain P ep i x v`, touching only the tweak, `CUR` and `OUT`.

  Two implementations (`chainWalkA`, `chainWalkB`) are proved against the
  same contract `ChainWalkPost` (PLAN M3). Each theorem assumes only that its
  own instructions sit at `idxChainWalk` (`CodeAt`), so a caller selects an
  implementation by choosing `chainWalk` and `chainWalk_correct`. LEGACY file.
-/

import XmssAsm.Regions.Common

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- The write set of a chain walk: the tweak, `CUR`, and `OUT`. -/
def WChain (a : Word) : Prop := InRange BUFA 16 a ∨ InRange CUR 16 a ∨ InRange OUT 32 a

/-- Loop registers of the caller a chain walk leaves alone. -/
def ChainKeep (s0 s : MachineState) : Prop :=
  s.getReg .x8 = s0.getReg .x8 ∧ s.getReg .x13 = s0.getReg .x13 ∧ s.getReg .x16 = s0.getReg .x16 ∧
  s.getReg .x18 = s0.getReg .x18 ∧ s.getReg .x19 = s0.getReg .x19

/-- The chain-walk contract, shared by both implementations: the region ends
    at `pcEnd` with `CUR = recoverChain`, the caller's registers kept, `P` in
    place, and nothing outside `WChain` written. -/
def ChainWalkPost (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (pcEnd : Word) (s : MachineState) :
    Prop :=
  s.pc = pcEnd ∧ ChainKeep s0 s ∧ HasDigest s BUFA_P P ∧
  HasDigest s CUR (recoverD H P ep ci x v) ∧ Frame WChain s0 s

/-- The precondition shared by both implementations. -/
def ChainWalkPre (s : MachineState) (P : PublicParameter) (ep : Epoch) (ci : ChainIndex)
    (x : Digit) (v : Digest) : Prop :=
  s.pc = addr idxChainWalk ∧ s.getReg .x8 = BitVec.ofNat 64 ep.val ∧
  s.getReg .x14 = BitVec.ofNat 64 x.val ∧ s.getReg .x16 = BitVec.ofNat 64 (8 * ci.val) ∧
  HasDigest s BUFA_P P ∧ HasDigest s CUR v

theorem digit_lt (x : Digit) : x.val < 8 := x.isLt

/-! ## Implementation A: header-guarded loop, constants reloaded per step -/

/-- The loop invariant of `chainWalkA` at its header (`BGE`), after `k` steps. -/
def ChainInvA (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (k : Nat) (s : MachineState) : Prop :=
  s.code = s0.code ∧ s.pc = addr (idxChainWalk + 2) ∧
  s.getReg .x8 = BitVec.ofNat 64 ep.val ∧ s.getReg .x16 = BitVec.ofNat 64 (8 * ci.val) ∧
  s.getReg .x15 = BitVec.ofNat 64 (x.val + k) ∧ s.getReg .x17 = 7#64 ∧
  HasDigest s BUFA_P P ∧
  HasDigest s CUR (walkD H P ep ci x.val k v) ∧ ChainKeep s0 s ∧ Frame WChain s0 s

theorem chainWalkA_entry (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChainWalk) chainWalkA 0) (P : PublicParameter) (ep : Epoch)
    (ci : ChainIndex) (x : Digit) (v : Digest) (hpre : ChainWalkPre s P ep ci x v) :
    Runs H s (ChainInvA H s P ep ci x v 0) := by
  obtain ⟨hpc, h8, h14, h16, hP, hv⟩ := hpre
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest] at hP hv
  sym_norm at hpc h8 h14 h16 hP hv
  subst hpc
  sym_code hC [chainWalkA] [chainStepA]
  obtain ⟨f0, f1, -⟩ := hC
  sym_plain_f f0; sym_plain_f f1
  refine Runs.done ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm; exact h8
  · sym_norm; exact h16
  · sym_norm; rw [h14, Nat.add_zero]
  · sym_norm
  · simp only [HasDigest]; sym_norm; exact hP
  · simp only [HasDigest, walkD_zero]; sym_norm; exact hv
  · simp only [ChainKeep]; sym_norm; exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  · sym_frame_W WChain

set_option maxRecDepth 4000 in
theorem chainStepA_body (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxChainWalk) chainWalkA 0) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (k : Nat) (hk : k < 7 - x.val)
    (s : MachineState) (hI : ChainInvA H s0 P ep ci x v k s) :
    Runs H s (ChainInvA H s0 P ep ci x v (k + 1)) := by
  obtain ⟨hcode, hpc, h8, h16, h15, h17, hP, hcur, hkeep, hfr⟩ := hI
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest, ChainKeep] at hP hcur hkeep
  sym_norm at hcode hpc h8 h16 h15 h17 hP hcur
  sym_norm at hkeep
  subst hpc
  rw [← hcode] at hC
  sym_code hC [chainWalkA] [chainStepA]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, -⟩ := hC
  have hx : x.val + k < 7 := by omega
  have hb : (R .x15).slt (R .x17) = true := by
    rw [h15, h17, slt_ofNat _ _ (by omega) (by omega)]; simp; omega
  sym_plain_f f2
  simp only [hb]; sym_norm
  sym_plain_f f3; sym_plain_f f4; sym_plain_f f5; sym_plain_f f6
  sym_sd_f f7
  sym_plain_f f8
  sym_sd_f f9
  sym_plain_f f10; sym_plain_f f11; sym_plain_f f12; sym_plain_f f13
  sym_hash_in_f f14 (wordsBytes [tw0 1 (8 * ci.val + (x.val + k)), tw1 ep.val, dLo P, dHi P,
    dLo (walkD H P ep ci x.val k v), dHi (walkD H P ep ci x.val k v)])
  case hin =>
    rw [hashInputOf_eq _ 6 (by sym_norm) (by sym_norm) (by sym_norm)]
    simp only [MachineState.readWords_succ, MachineState.readWords_zero]
    sym_norm
    simp only [h16, h15, h8, hP.1, hP.2, hcur.1, hcur.2, tw0_machine, tw1_machine]
  sym_plain_f f15
  sym_ld_f f16; sym_ld_f f17; sym_sd_f f18; sym_sd_f f19
  sym_plain_f f20; sym_plain_f f21
  refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm; exact h8
  · sym_norm; exact h16
  · sym_norm; rw [h15]; exact ofNat_add_one _ _
  · sym_norm; exact h17
  · simp only [HasDigest]; sym_norm; exact hP
  · simp only [HasDigest]; sym_norm
    rw [walkD_succ _ _ _ _ _ _ _ hx, dLo_truncateHash, dHi_truncateHash]
    exact ⟨rfl, rfl⟩
  · simp only [ChainKeep]; sym_norm; exact hkeep
  · exact Frame.trans hfr (by sym_frame_W WChain)

theorem chainWalkA_exit (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxChainWalk) chainWalkA 0) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (s : MachineState)
    (hI : ChainInvA H s0 P ep ci x v (7 - x.val) s) :
    Runs H s (ChainWalkPost H s0 P ep ci x v (addr (idxChainWalk + chainWalkA.length))) := by
  obtain ⟨hcode, hpc, h8, h16, h15, h17, hP, hcur, hkeep, hfr⟩ := hI
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest, ChainKeep] at hP hcur hkeep
  sym_norm at hcode hpc h8 h16 h15 h17 hP hcur
  sym_norm at hkeep
  subst hpc
  rw [← hcode] at hC
  sym_code hC [chainWalkA] [chainStepA]
  obtain ⟨-, -, f2, -⟩ := hC
  have hx8 := digit_lt x
  have hb : (R .x15).slt (R .x17) = false := by
    rw [h15, h17, slt_ofNat _ _ (by omega) (by omega)]; simp; omega
  sym_plain_f f2
  simp only [hb]; sym_norm
  refine Runs.done ⟨?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · simp only [ChainKeep]; sym_norm; exact hkeep
  · simp only [HasDigest]; sym_norm; exact hP
  · simp only [HasDigest, recoverD_eq]; sym_norm; exact hcur
  · exact Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Implementation A satisfies the chain-walk contract. -/
theorem chainWalkA_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChainWalk) chainWalkA 0) (P : PublicParameter) (ep : Epoch)
    (ci : ChainIndex) (x : Digit) (v : Digest) (hpre : ChainWalkPre s P ep ci x v) :
    Runs H s (ChainWalkPost H s P ep ci x v (addr (idxChainWalk + chainWalkA.length))) :=
  Runs.bind (chainWalkA_entry H s hC P ep ci x v hpre) fun s1 h1 =>
    Runs.bind
      (Runs.loop (7 - x.val) (fun k s' hk hI => chainStepA_body H s hC P ep ci x v k hk s' hI) s1 h1)
      fun s2 h2 => chainWalkA_exit H s hC P ep ci x v s2 h2

/-! ## Implementation B: constants hoisted, position and bound kept in registers -/

/-- The loop invariant of `chainWalkB` at its header (`BGE`), after `k` steps. -/
def ChainInvB (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (k : Nat) (s : MachineState) : Prop :=
  s.code = s0.code ∧ s.pc = addr (idxChainWalk + 9) ∧
  s.getReg .x7 = BUFA ∧ s.getReg .x5 = HASH_ID ∧ s.getReg .x10 = BUFA ∧ s.getReg .x11 = 48#64 ∧
  s.getReg .x12 = OUT ∧
  s.getReg .x8 = BitVec.ofNat 64 ep.val ∧ s.getReg .x16 = BitVec.ofNat 64 (8 * ci.val) ∧
  s.getReg .x15 = BitVec.ofNat 64 (8 * ci.val + x.val + k) ∧
  s.getReg .x17 = BitVec.ofNat 64 (8 * ci.val + 7) ∧
  HasDigest s BUFA_P P ∧ s.getMem (BUFA + 8) = tw1 ep.val ∧
  HasDigest s CUR (walkD H P ep ci x.val k v) ∧ ChainKeep s0 s ∧ Frame WChain s0 s

theorem chainWalkB_entry (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChainWalk) chainWalkB 0) (P : PublicParameter) (ep : Epoch)
    (ci : ChainIndex) (x : Digit) (v : Digest) (hpre : ChainWalkPre s P ep ci x v) :
    Runs H s (ChainInvB H s P ep ci x v 0) := by
  obtain ⟨hpc, h8, h14, h16, hP, hv⟩ := hpre
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest] at hP hv
  sym_norm at hpc h8 h14 h16 hP hv
  subst hpc
  sym_code hC [chainWalkB] [chainStepB]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := hC
  sym_plain_f f0; sym_plain_f f1; sym_plain_f f2; sym_plain_f f3; sym_plain_f f4; sym_plain_f f5
  sym_sd_f f6
  sym_plain_f f7; sym_plain_f f8
  refine Runs.done ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm; exact h8
  · sym_norm; exact h16
  · sym_norm; rw [h16, h14, ← BitVec.ofNat_add, Nat.add_zero]
  · sym_norm; rw [h16, BitVec.ofNat_add]
  · simp only [HasDigest]; sym_norm; exact hP
  · sym_norm; rw [h8, tw1_machine]
  · simp only [HasDigest, walkD_zero]; sym_norm; exact hv
  · simp only [ChainKeep]; sym_norm; exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  · sym_frame_W WChain

set_option maxRecDepth 4000 in
theorem chainStepB_body (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxChainWalk) chainWalkB 0) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (k : Nat) (hk : k < 7 - x.val)
    (s : MachineState) (hI : ChainInvB H s0 P ep ci x v k s) :
    Runs H s (ChainInvB H s0 P ep ci x v (k + 1)) := by
  obtain ⟨hcode, hpc, h7, h5, h10, h11, h12, h8, h16, h15, h17, hP, htw, hcur, hkeep, hfr⟩ := hI
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest, ChainKeep] at hP hcur hkeep
  sym_norm at hcode hpc h7 h5 h10 h11 h12 h8 h16 h15 h17 hP htw hcur
  sym_norm at hkeep
  subst hpc
  rw [← hcode] at hC
  sym_code hC [chainWalkB] [chainStepB]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    -⟩ := hC
  have hR : R = fun r => if r = .x7 then BUFA else if r = .x5 then HASH_ID else
      if r = .x10 then BUFA else if r = .x11 then 48#64 else if r = .x12 then OUT else R r := by
    funext r
    split_ifs <;> subst_vars <;> first | exact h7 | exact h5 | exact h10 | exact h11 | exact h12 | rfl
  have hx : x.val + k < 7 := by omega
  have hci : ci.val < 42 := ci.isLt
  have hb : (R .x15).slt (R .x17) = true := by
    rw [h15, h17, slt_ofNat _ _ (by omega) (by omega)]; simp; omega
  rw [hR]
  sym_plain_f f9
  simp only [hb]; sym_norm
  sym_plain_f f10; sym_plain_f f11
  sym_sd_f f12
  sym_hash_in_f f13 (wordsBytes [tw0 1 (8 * ci.val + (x.val + k)), tw1 ep.val, dLo P, dHi P,
    dLo (walkD H P ep ci x.val k v), dHi (walkD H P ep ci x.val k v)])
  case hin =>
    rw [hashInputOf_eq _ 6 (by sym_norm) (by sym_norm) (by sym_norm)]
    simp only [MachineState.readWords_succ, MachineState.readWords_zero]
    sym_norm
    simp only [h15, hP.1, hP.2, hcur.1, hcur.2, htw, tw0_machine', Nat.add_assoc]
  sym_ld_f f14; sym_ld_f f15; sym_sd_f f16; sym_sd_f f17
  sym_plain_f f18; sym_plain_f f19
  refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm; exact h8
  · sym_norm; exact h16
  · sym_norm; rw [h15]; exact ofNat_add_one _ _
  · sym_norm; exact h17
  · simp only [HasDigest]; sym_norm; exact hP
  · sym_norm; exact htw
  · simp only [HasDigest]; sym_norm
    rw [walkD_succ _ _ _ _ _ _ _ hx, dLo_truncateHash, dHi_truncateHash]
    exact ⟨rfl, rfl⟩
  · simp only [ChainKeep]; sym_norm; exact hkeep
  · exact Frame.trans hfr (by sym_frame_W WChain)

theorem chainWalkB_exit (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxChainWalk) chainWalkB 0) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (s : MachineState)
    (hI : ChainInvB H s0 P ep ci x v (7 - x.val) s) :
    Runs H s (ChainWalkPost H s0 P ep ci x v (addr (idxChainWalk + chainWalkB.length))) := by
  obtain ⟨hcode, hpc, -, -, -, -, -, -, -, h15, h17, hP, -, hcur, hkeep, hfr⟩ := hI
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest, ChainKeep] at hP hcur hkeep
  sym_norm at hcode hpc h15 h17 hP hcur
  sym_norm at hkeep
  subst hpc
  rw [← hcode] at hC
  sym_code hC [chainWalkB] [chainStepB]
  obtain ⟨-, -, -, -, -, -, -, -, -, f9, -⟩ := hC
  have hx8 := digit_lt x
  have hci : ci.val < 42 := ci.isLt
  have hb : (R .x15).slt (R .x17) = false := by
    rw [h15, h17, slt_ofNat _ _ (by omega) (by omega)]; simp; omega
  sym_plain_f f9
  simp only [hb]; sym_norm
  refine Runs.done ⟨?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · simp only [ChainKeep]; sym_norm; exact hkeep
  · simp only [HasDigest]; sym_norm; exact hP
  · simp only [HasDigest, recoverD_eq]; sym_norm; exact hcur
  · exact Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Implementation B satisfies the same chain-walk contract. -/
theorem chainWalkB_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChainWalk) chainWalkB 0) (P : PublicParameter) (ep : Epoch)
    (ci : ChainIndex) (x : Digit) (v : Digest) (hpre : ChainWalkPre s P ep ci x v) :
    Runs H s (ChainWalkPost H s P ep ci x v (addr (idxChainWalk + chainWalkB.length))) :=
  Runs.bind (chainWalkB_entry H s hC P ep ci x v hpre) fun s1 h1 =>
    Runs.bind
      (Runs.loop (7 - x.val) (fun k s' hk hI => chainStepB_body H s hC P ep ci x v k hk s' hI) s1 h1)
      fun s2 h2 => chainWalkB_exit H s hC P ep ci x v s2 h2

/-! ## The selected implementation

Callers use only `chainWalk_correct`; swapping A for B changes this
definition, `chainWalk`, `chainWalk_length` and `bOff_chainsLoop`. -/

theorem chainWalk_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChainWalk) chainWalk 0) (P : PublicParameter) (ep : Epoch)
    (ci : ChainIndex) (x : Digit) (v : Digest) (hpre : ChainWalkPre s P ep ci x v) :
    Runs H s (ChainWalkPost H s P ep ci x v (addr idxChainStore)) :=
  chainWalkA_correct H s hC P ep ci x v hpre

end XmssAsm
