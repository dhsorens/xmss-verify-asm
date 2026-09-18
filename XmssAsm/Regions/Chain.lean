/-
  XmssAsm.Regions.Chain

  The chain-walk region. From `x14 = x`, `x16 = 8 i`, `x8 = ep`, `CUR = v`,
  `BUFA_P = P`, execution reaches the instruction after the region with
  `CUR = recoverChain P ep i x v`, touching only the tweak, `CUR` and `OUT`.

  The theorem assumes only that the walk's own instructions sit at
  `idxChainWalk` (`CodeAt`), so it says nothing about the rest of the
  program and callers depend on `ChainWalkPost` alone. M3 validated this
  boundary with a second implementation behind the same contract; M8.a
  collapsed that dual, and git history keeps the experiment. LEGACY file.
-/

import XmssAsm.Regions.Common

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- The write set of a chain walk: the tweak doublewords of `BUFA`, and the
    32 bytes at `CUR`.

    `CUR` rather than `OUT` because the oracle now writes its output block
    directly into the payload slot (`chainStep`), and 32 bytes rather than 16
    because that block is a full hash output: the digest lands in the payload
    slot and its unused upper half in `CUR2`. Both are scratch, so the
    top-level `Frame InScratch` is unaffected, but this *is* a weaker frame at
    `CUR2` than the copy-based walk gave, and callers may no longer assume
    `CUR2` survives a chain walk (none does; the auth region writes it itself).
    Correspondingly the walk no longer touches `OUT` at all. -/
def WChain (a : Word) : Prop := InRange BUFA 16 a ∨ InRange CUR 32 a

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

/-! ## The walk: constants hoisted, position and bound kept in registers -/

/-- The loop invariant of `chainWalk` after `k` steps.

    The loop is rotated, so the invariant is stated at the *first instruction
    of the body* while steps remain, and at the instruction after the region
    once they do not. One `if` covers both, and then each of the three parts of
    the proof reads off the boundary it needs: the header `BGE` lands on
    whichever arm `k = 0` selects, the bottom `BLT` on whichever arm `k + 1`
    selects, and the exit is the `k = 7 - x` case with nothing left to run. -/
def ChainInv (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (k : Nat) (s : MachineState) : Prop :=
  s.code = s0.code ∧
  s.pc = (if k < 7 - x.val then addr (idxChainWalk + 10)
          else addr (idxChainWalk + chainWalk.length)) ∧
  s.getReg .x7 = BUFA ∧ s.getReg .x5 = HASH_ID ∧ s.getReg .x10 = BUFA ∧ s.getReg .x11 = 48#64 ∧
  s.getReg .x12 = CUR ∧
  s.getReg .x8 = BitVec.ofNat 64 ep.val ∧ s.getReg .x16 = BitVec.ofNat 64 (8 * ci.val) ∧
  s.getReg .x15 = BitVec.ofNat 64 (8 * ci.val + x.val + k) ∧
  s.getReg .x17 = BitVec.ofNat 64 (8 * ci.val + 7) ∧
  HasDigest s BUFA_P P ∧ s.getMem (BUFA + 8) = tw1 ep.val ∧
  HasDigest s CUR (walkD H P ep ci x.val k v) ∧ ChainKeep s0 s ∧ Frame WChain s0 s

theorem chainWalk_entry (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChainWalk) chainWalk 0) (P : PublicParameter) (ep : Epoch)
    (ci : ChainIndex) (x : Digit) (v : Digest) (hpre : ChainWalkPre s P ep ci x v) :
    Runs H s (ChainInv H s P ep ci x v 0) := by
  obtain ⟨hpc, h8, h14, h16, hP, hv⟩ := hpre
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest] at hP hv
  sym_norm at hpc h8 h14 h16 hP hv
  subst hpc
  sym_code hC [chainWalk] [chainStep]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, -⟩ := hC
  have hci : ci.val < 42 := ci.isLt
  have hx8 := digit_lt x
  -- the header guard, in terms of the digit: the walk has length `7 - x`
  have hslt : (R .x16 + R .x14).slt (R .x16 + 7#64) = decide (8 * ci.val + x.val < 8 * ci.val + 7) := by
    rw [h16, h14, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      slt_ofNat _ _ (by omega) (by omega)]
  sym_plain_f f0; sym_plain_f f1; sym_plain_f f2; sym_plain_f f3; sym_plain_f f4; sym_plain_f f5
  sym_sd_f f6
  sym_plain_f f7; sym_plain_f f8
  sym_plain_f f9
  by_cases hx7 : x.val < 7
  · have hb : (R .x16 + R .x14).slt (R .x16 + 7#64) = true := by
      rw [hslt]; exact decide_eq_true (by omega)
    rw [if_neg (not_not_intro hb)]
    refine Runs.done ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos (by omega)]; sym_norm
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
  · have hb : (R .x16 + R .x14).slt (R .x16 + 7#64) = false := by
      rw [hslt]; exact decide_eq_false (by omega)
    rw [if_pos (by rw [hb]; exact Bool.false_ne_true)]
    refine Runs.done ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (by omega)]; sym_norm
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
theorem chainStep_body (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxChainWalk) chainWalk 0) (P : PublicParameter)
    (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest) (k : Nat) (hk : k < 7 - x.val)
    (s : MachineState) (hI : ChainInv H s0 P ep ci x v k s) :
    Runs H s (ChainInv H s0 P ep ci x v (k + 1)) := by
  obtain ⟨hcode, hpc, h7, h5, h10, h11, h12, h8, h16, h15, h17, hP, htw, hcur, hkeep, hfr⟩ := hI
  rw [if_pos hk] at hpc
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest, ChainKeep] at hP hcur hkeep
  sym_norm at hcode hpc h7 h5 h10 h11 h12 h8 h16 h15 h17 hP htw hcur
  sym_norm at hkeep
  subst hpc
  rw [← hcode] at hC
  sym_code hC [chainWalk] [chainStep]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, f10, f11, f12, f13, f14, f15, -⟩ := hC
  have hR : R = fun r => if r = .x7 then BUFA else if r = .x5 then HASH_ID else
      if r = .x10 then BUFA else if r = .x11 then 48#64 else if r = .x12 then CUR else R r := by
    funext r
    split_ifs <;> subst_vars <;> first | exact h7 | exact h5 | exact h10 | exact h11 | exact h12 | rfl
  have hx : x.val + k < 7 := by omega
  have hci : ci.val < 42 := ci.isLt
  have hx8 := digit_lt x
  -- the bottom branch, in terms of whether another step remains
  have hslt : (R .x15 + 1#64).slt (R .x17)
      = decide (8 * ci.val + x.val + k + 1 < 8 * ci.val + 7) := by
    rw [h15, h17, ← BitVec.ofNat_add, slt_ofNat _ _ (by omega) (by omega)]
  rw [hR]
  sym_plain_f f10; sym_plain_f f11
  sym_sd_f f12
  sym_hash_in_f f13 (wordsBytes [tw0 1 (8 * ci.val + (x.val + k)), tw1 ep.val, dLo P, dHi P,
    dLo (walkD H P ep ci x.val k v), dHi (walkD H P ep ci x.val k v)])
  case hin =>
    rw [hashInputOf_eq _ 6 (by sym_norm) (by sym_norm) (by sym_norm)]
    simp only [MachineState.readWords_succ, MachineState.readWords_zero]
    sym_norm
    simp only [h15, hP.1, hP.2, hcur.1, hcur.2, htw, tw0_machine', Nat.add_assoc]
  sym_plain_f f14
  sym_plain_f f15
  by_cases hk1 : k + 1 < 7 - x.val
  · have hb : (R .x15 + 1#64).slt (R .x17) = true := by
      rw [hslt]; exact decide_eq_true (by omega)
    rw [if_pos hb]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos hk1]; sym_norm
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
  · have hb : (R .x15 + 1#64).slt (R .x17) = false := by
      rw [hslt]; exact decide_eq_false (by omega)
    rw [if_neg (by rw [hb]; exact Bool.false_ne_true)]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hk1]; sym_norm
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

/-- The exit. With the branch at the bottom there is nothing left to execute:
    the last iteration's `BLT` already fell through to the instruction after
    the region, which is what `ChainInv (7 - x)` says. -/
theorem chainWalk_exit (H : HashInput → HashOutput) (s0 : MachineState)
    (P : PublicParameter) (ep : Epoch) (ci : ChainIndex) (x : Digit) (v : Digest)
    (s : MachineState) (hI : ChainInv H s0 P ep ci x v (7 - x.val) s) :
    Runs H s (ChainWalkPost H s0 P ep ci x v (addr (idxChainWalk + chainWalk.length))) := by
  obtain ⟨-, hpc, -, -, -, -, -, -, -, -, -, hP, -, hcur, hkeep, hfr⟩ := hI
  rw [if_neg (by omega)] at hpc
  exact Runs.done ⟨hpc, hkeep, hP, by simpa only [recoverD_eq] using hcur, hfr⟩

/-- The chain walk satisfies its contract. Callers use only this theorem. -/
theorem chainWalk_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChainWalk) chainWalk 0) (P : PublicParameter) (ep : Epoch)
    (ci : ChainIndex) (x : Digit) (v : Digest) (hpre : ChainWalkPre s P ep ci x v) :
    Runs H s (ChainWalkPost H s P ep ci x v (addr (idxChainWalk + chainWalk.length))) :=
  Runs.bind (chainWalk_entry H s hC P ep ci x v hpre) fun s1 h1 =>
    Runs.bind
      (Runs.loop (7 - x.val) (fun k s' hk hI => chainStep_body H s hC P ep ci x v k hk s' hI) s1 h1)
      fun s2 h2 => chainWalk_exit H s P ep ci x v s2 h2

end XmssAsm
