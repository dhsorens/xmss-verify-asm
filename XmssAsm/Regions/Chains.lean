/-
  XmssAsm.Regions.Chains

  The 42-chain loop: for each chain `i`, load `sig.chainValue i` into `CUR`
  and the digit into `x14`, run the chain walk (through `chainWalk_correct`,
  the only fact about the walk this file uses), and store `CUR` as endpoint
  `i`. LEGACY file.
-/

import XmssAsm.Regions.Chain

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- The write set of the chains region: the chain walk's, plus the endpoints. -/
def WChains (a : Word) : Prop := WChain a ∨ InRange ENDPTS 672 a

theorem not_WChains_bufaP : ¬ WChains BUFA_P ∧ ¬ WChains (BUFA_P + 8) := by
  simp only [WChains, WChain, InRange, not_or, BUFA, CUR, OUT, ENDPTS, BUFA_P]; decide

theorem not_WChains_chains (i : Nat) (hi : i < 42) :
    ¬ WChains (CHAINS + BitVec.ofNat 64 (16 * i)) ∧ ¬ WChains (CHAINS + BitVec.ofNat 64 (16 * i) + 8) := by
  simp only [WChains, WChain, InRange, not_or, BUFA, CUR, OUT, ENDPTS, CHAINS]; bv_omega

theorem not_WChains_digits (i : Nat) (hi : i < 42) : ¬ WChains (DIGITS + BitVec.ofNat 64 (8 * i)) := by
  simp only [WChains, WChain, InRange, not_or, BUFA, CUR, OUT, ENDPTS, DIGITS]; bv_omega

theorem not_WChain_endpts (j : Nat) (hj : j < 42) :
    ¬ WChain (ENDPTS + BitVec.ofNat 64 (16 * j)) ∧ ¬ WChain (ENDPTS + BitVec.ofNat 64 (16 * j) + 8) := by
  simp only [WChain, InRange, not_or, BUFA, CUR, OUT, ENDPTS]; bv_omega

/-- A valid access at `literal + ofNat k` or `literal + ofNat k + 8`. -/
macro "sym_valid_off" : tactic =>
  `(tactic| ((try sym_norm); first
    | exact XmssAsm.valid_off _ _ (by decide) (by decide) (by omega) (by simp only [BitVec.reduceToNat]; omega)
    | exact XmssAsm.valid_off8 _ _ (by decide) (by decide) (by omega) (by simp only [BitVec.reduceToNat]; omega)))

/-- The loop invariant at the head of the chains loop after `i` chains (at
    `idxLeaf` once all 42 are done). -/
def ChainsInv (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter) (ep : Epoch)
    (enc : Encoding) (cv : ChainIndex → Digest) (i : Nat) (s : MachineState) : Prop :=
  s.code = s0.code ∧ s.pc = (if i < 42 then addr idxChainsLoop else addr idxLeaf) ∧
  s.getReg .x8 = BitVec.ofNat 64 ep.val ∧ s.getReg .x13 = BitVec.ofNat 64 i ∧
  s.getReg .x16 = BitVec.ofNat 64 (8 * i) ∧ s.getReg .x18 = ENDPTS + BitVec.ofNat 64 (16 * i) ∧
  s.getReg .x19 = DIGITS + BitVec.ofNat 64 (8 * i) ∧
  (∀ j : ChainIndex, j.val < i →
    HasDigest s (ENDPTS + BitVec.ofNat 64 (16 * j.val)) (recoverD H P ep j (enc j) (cv j))) ∧
  Frame WChains s0 s

/-- The chains contract: every endpoint recovered, `x8` kept, frame `WChains`. -/
def ChainsPost (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter) (ep : Epoch)
    (enc : Encoding) (cv : ChainIndex → Digest) (s : MachineState) : Prop :=
  s.pc = addr idxLeaf ∧ s.getReg .x8 = BitVec.ofNat 64 ep.val ∧
  (∀ j : ChainIndex, HasDigest s (ENDPTS + BitVec.ofNat 64 (16 * j.val)) (recoverD H P ep j (enc j) (cv j))) ∧
  Frame WChains s0 s

theorem chains_entry (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxChains) chainsPre 0) (P : PublicParameter) (ep : Epoch)
    (enc : Encoding) (cv : ChainIndex → Digest) (hpc : s.pc = addr idxChains)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 ep.val) :
    Runs H s (ChainsInv H s P ep enc cv 0) := by
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  sym_norm at hpc h8
  subst hpc
  sym_code1 hC [chainsPre]
  obtain ⟨f0, f1, f2, f3, -⟩ := hC
  sym_plain_f f0; sym_plain_f f1; sym_plain_f f2; sym_plain_f f3
  refine Runs.done ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm; exact h8
  · sym_norm
  · sym_norm
  · sym_norm
  · sym_norm
  · intro j hj; exact absurd hj (Nat.not_lt_zero _)
  · sym_frame_W WChains

set_option maxRecDepth 4000 in
theorem chains_body (H : HashInput → HashOutput) (s0 : MachineState)
    (hC1 : CodeAt s0.code (addr idxChainsLoop) chainLoad 0)
    (hCW : CodeAt s0.code (addr idxChainWalk) chainWalk 0)
    (hC3 : CodeAt s0.code (addr idxChainStore) chainsTail 0)
    (P : PublicParameter) (ep : Epoch) (enc : Encoding) (cv : ChainIndex → Digest)
    (hP0 : HasDigest s0 BUFA_P P)
    (hcv0 : ∀ j : ChainIndex, HasDigest s0 (CHAINS + BitVec.ofNat 64 (16 * j.val)) (cv j))
    (hdig0 : ∀ j : ChainIndex, s0.getMem (DIGITS + BitVec.ofNat 64 (8 * j.val)) = BitVec.ofNat 64 (enc j).val)
    (i : Nat) (hi : i < 42) (s : MachineState) (hI : ChainsInv H s0 P ep enc cv i s) :
    Runs H s (ChainsInv H s0 P ep enc cv (i + 1)) := by
  obtain ⟨hcode, hpc, h8, h13, h16, h18, h19, hE, hfr⟩ := hI
  -- facts about `s` inherited from `s0` through the frame
  have hP : HasDigest s BUFA_P P :=
    ⟨(hfr.mem _ not_WChains_bufaP.1).trans hP0.1, (hfr.mem _ not_WChains_bufaP.2).trans hP0.2⟩
  have hcv : HasDigest s (CHAINS + BitVec.ofNat 64 (16 * i)) (cv ⟨i, hi⟩) :=
    ⟨(hfr.mem _ (not_WChains_chains i hi).1).trans (hcv0 ⟨i, hi⟩).1,
     (hfr.mem _ (not_WChains_chains i hi).2).trans (hcv0 ⟨i, hi⟩).2⟩
  have hdig : s.getMem (DIGITS + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 (enc ⟨i, hi⟩).val :=
    (hfr.mem _ (not_WChains_digits i hi)).trans (hdig0 ⟨i, hi⟩)
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  rw [if_pos hi] at hpc
  simp only [HasDigest] at hP hcv
  sym_norm at hcode hpc h8 h13 h16 h18 h19 hP hcv hdig
  subst hpc
  rw [← hcode] at hC1 hCW hC3
  sym_code1 hC1 [chainLoad]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := hC1
  -- chainLoad
  sym_plain_f f0; sym_plain_f f1
  simp only [h13, shl4_ofNat]
  sym_plain_f f2
  sym_ld_f_with f3 (by sym_valid_off); sym_ld_f_with f4 (by sym_valid_off)
  sym_plain_f f5; sym_sd_f f6; sym_sd_f f7
  sym_ld_f_with f8 (by sym_norm; rw [h19]; sym_valid_off)
  simp only [h19]
  -- the chain walk, through its contract only
  refine Runs.bind (chainWalk_correct H _ hCW P ep ⟨i, hi⟩ (enc ⟨i, hi⟩) (cv ⟨i, hi⟩) ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_norm
    · sym_norm; exact h8
    · sym_norm; simp (disch := bv_omega) only [if_neg]; exact hdig
    · sym_norm; exact h16
    · simp only [HasDigest]; sym_norm; exact hP
    · simp only [HasDigest]; sym_norm; exact hcv
  intro s2 hpost
  obtain ⟨hpc2, hkeep2, hP2, hcur2, hfr2⟩ := hpost
  obtain ⟨R2, M2, C2, pc2, c2, pv2, pi2, ib2⟩ := s2
  obtain ⟨hc2, hcm2, hpv2, hpi2, hib2, hmem2, hreg2⟩ := hfr2
  simp only [ChainKeep, HasDigest] at hkeep2 hP2 hcur2
  sym_norm at hpc2 hkeep2 hP2 hcur2 hc2 hcm2 hpv2 hpi2 hib2
  subst hpc2 hc2 hcm2 hpv2 hpi2 hib2
  obtain ⟨k8, k13, k16, k18, k19⟩ := hkeep2
  -- memory outside the walk's write set is the memory after `chainLoad`
  have hmem2' : ∀ a, ¬ WChain a → M2 a = M a := by
    intro a ha
    have := hmem2 a ha
    simp only [WChain, InRange, not_or] at ha
    sym_norm at ha this
    rw [this]
    simp (disch := bv_omega) only [if_neg]
  sym_code1 hC3 [chainsTail, chainStore]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -⟩ := hC3
  sym_plain_f g0; sym_ld_f g1; sym_ld_f g2
  sym_sd_f_with g3 (by sym_norm; rw [k18, h18]; sym_valid_off)
  sym_sd_f_with g4 (by sym_norm; rw [k18, h18]; sym_valid_off)
  simp only [k18, h18]
  sym_plain_f g5; sym_plain_f g6; sym_plain_f g7; sym_plain_f g8; sym_plain_f g9
  simp only [k13, h13, k16, h16, k19, h19, ofNat_succ]
  sym_plain_f g10
  simp only [k18, h18]
  -- the invariant at `i + 1`, whichever way the branch goes
  have hx16 : BitVec.ofNat 64 (8 * i) + 8#64 = BitVec.ofNat 64 (8 * (i + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hx18 : 67424#64 + BitVec.ofNat 64 (16 * i) + 16#64 = 67424#64 + BitVec.ofNat 64 (16 * (i + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hx19 : 66944#64 + BitVec.ofNat 64 (8 * i) + 8#64 = 66944#64 + BitVec.ofNat 64 (8 * (i + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hEnd : ∀ j : ChainIndex, j.val < i + 1 →
      (if 67424#64 + BitVec.ofNat 64 (16 * j.val) = 67424#64 + BitVec.ofNat 64 (16 * i) + 8#64 then M2 66856#64
        else if 67424#64 + BitVec.ofNat 64 (16 * j.val) = 67424#64 + BitVec.ofNat 64 (16 * i) then M2 66848#64
        else M2 (67424#64 + BitVec.ofNat 64 (16 * j.val))) = dLo (recoverD H P ep j (enc j) (cv j)) ∧
      (if 67424#64 + BitVec.ofNat 64 (16 * j.val) + 8#64 = 67424#64 + BitVec.ofNat 64 (16 * i) + 8#64 then
          M2 66856#64
        else if 67424#64 + BitVec.ofNat 64 (16 * j.val) + 8#64 = 67424#64 + BitVec.ofNat 64 (16 * i) then
          M2 66848#64
        else M2 (67424#64 + BitVec.ofNat 64 (16 * j.val) + 8#64)) = dHi (recoverD H P ep j (enc j) (cv j)) := by
    intro j hj
    have hj42 : j.val < 42 := j.isLt
    rcases Nat.lt_or_ge j.val i with hji | hji
    · simp (disch := bv_omega) only [if_neg]
      have e1 := hmem2' _ (not_WChain_endpts j.val hj42).1
      have e2 := hmem2' _ (not_WChain_endpts j.val hj42).2
      sym_norm at e1 e2
      rw [e1, e2]
      have := hE j hji
      simp only [HasDigest] at this
      sym_norm at this
      exact this
    · have hji' : j = ⟨i, hi⟩ := Fin.ext (by dsimp only; omega)
      subst hji'
      dsimp only
      have t1 : ¬ (67424#64 + BitVec.ofNat 64 (16 * i) = 67424#64 + BitVec.ofNat 64 (16 * i) + 8#64) := by
        addr_ne
      simp only [t1, ↓reduceIte]
      exact hcur2
  have hFr : Frame WChains s0
      ⟨fun r' => if r' = .x6 then 42#64 else if r' = .x16 then BitVec.ofNat 64 (8 * i) + 8#64 else
        if r' = .x19 then 66944#64 + BitVec.ofNat 64 (8 * i) + 8#64 else
        if r' = .x18 then 67424#64 + BitVec.ofNat 64 (16 * i) + 16#64 else
        if r' = .x13 then BitVec.ofNat 64 (i + 1) else if r' = .x29 then M2 66856#64 else
        if r' = .x28 then M2 66848#64 else if r' = .x6 then 66848#64 else R2 r',
       fun a' => if a' = 67424#64 + BitVec.ofNat 64 (16 * i) + 8#64 then M2 66856#64 else
        if a' = 67424#64 + BitVec.ofNat 64 (16 * i) then M2 66848#64 else M2 a',
       C2, 0, c2, pv2, pi2, ib2⟩ := by
    refine Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro a ha
      have hm := hmem2' a (fun h => ha (Or.inl h))
      simp only [WChains, WChain, InRange, not_or] at ha
      sym_norm at ha
      sym_norm
      have t1 : ¬ (a = 67424#64 + BitVec.ofNat 64 (16 * i) + 8#64) := by addr_ne
      have t2 : ¬ (a = 67424#64 + BitVec.ofNat 64 (16 * i)) := by addr_ne
      simp only [t1, t2, ↓reduceIte]
      exact hm
    · intro r hr
      have hrg := hreg2 r hr
      simp only [CLOB, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      sym_norm at hrg
      simp only [hr, ↓reduceIte] at hrg
      sym_norm
      simp only [hr, ↓reduceIte]
      exact hrg
  rcases Nat.lt_or_ge (i + 1) 42 with hlt | hge
  · have hne : ¬ BitVec.ofNat 64 (i + 1) = 42#64 := by
      intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    rw [if_pos hne]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_norm; rw [if_pos hlt]
    · sym_norm; rw [k8]; exact h8
    · sym_norm
    · sym_norm; exact hx16
    · sym_norm; exact hx18
    · sym_norm; exact hx19
    · intro j hj; simp only [HasDigest]; sym_norm; exact hEnd j hj
    · exact ⟨hFr.1, hFr.2.1, hFr.2.2.1, hFr.2.2.2.1, hFr.2.2.2.2.1, hFr.2.2.2.2.2.1, hFr.2.2.2.2.2.2⟩
  · have heq : BitVec.ofNat 64 (i + 1) = 42#64 := by
      rw [show i + 1 = 42 by omega]
    rw [if_neg (not_not_intro heq)]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_norm; rw [if_neg (by omega)]
    · sym_norm; rw [k8]; exact h8
    · sym_norm
    · sym_norm; exact hx16
    · sym_norm; exact hx18
    · sym_norm; exact hx19
    · intro j hj; simp only [HasDigest]; sym_norm; exact hEnd j hj
    · exact ⟨hFr.1, hFr.2.1, hFr.2.2.1, hFr.2.2.2.1, hFr.2.2.2.2.1, hFr.2.2.2.2.2.1, hFr.2.2.2.2.2.2⟩

/-- The chains region: all 42 endpoints recovered. -/
theorem chains_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC0 : CodeAt s.code (addr idxChains) chainsPre 0)
    (hC1 : CodeAt s.code (addr idxChainsLoop) chainLoad 0)
    (hCW : CodeAt s.code (addr idxChainWalk) chainWalk 0)
    (hC3 : CodeAt s.code (addr idxChainStore) chainsTail 0)
    (P : PublicParameter) (ep : Epoch) (enc : Encoding) (cv : ChainIndex → Digest)
    (hpc : s.pc = addr idxChains) (h8 : s.getReg .x8 = BitVec.ofNat 64 ep.val)
    (hP0 : HasDigest s BUFA_P P)
    (hcv0 : ∀ j : ChainIndex, HasDigest s (CHAINS + BitVec.ofNat 64 (16 * j.val)) (cv j))
    (hdig0 : ∀ j : ChainIndex, s.getMem (DIGITS + BitVec.ofNat 64 (8 * j.val)) = BitVec.ofNat 64 (enc j).val) :
    Runs H s (ChainsPost H s P ep enc cv) :=
  Runs.bind (chains_entry H s hC0 P ep enc cv hpc h8) fun s1 h1 =>
    Runs.mono
      (Runs.loop 42 (fun i s' hi hI => chains_body H s hC1 hCW hC3 P ep enc cv hP0 hcv0 hdig0 i hi s' hI) s1 h1)
      fun s' hI => ⟨hI.2.1.trans (if_neg (by decide)), hI.2.2.1,
        fun j => hI.2.2.2.2.2.2.2.1 j (j.isLt : j.val < 42), hI.2.2.2.2.2.2.2.2⟩

end XmssAsm
