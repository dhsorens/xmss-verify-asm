/-
  XmssAsm.Regions.Decode

  The decode region: reject if either padding bit is set, extract the 42
  three-bit digits of the encoding digest into `DIGITS` while summing them,
  reject unless the sum is 195, else continue at `idxChains`. The contract is
  `decodeDigest`, case by case. LEGACY file.
-/

import XmssAsm.Spec.Decode

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- The write set of `decode`: the 42 digit doublewords. -/
def WDecode (a : Word) : Prop := InRange DIGITS 336 a

/-- The machine halted at the reject stub with `a0 = 0`. -/
def Rejected (H : HashInput → HashOutput) (s0 s : MachineState) : Prop :=
  Decomp.SyscallHalted s ∧ stepH H s = none ∧ s.getReg .x10 = 0 ∧ Frame WDecode s0 s

/-- The digest decoded to `enc`: the digits are in `DIGITS`, `x8` kept. -/
def DecodeAccept (s0 : MachineState) (enc : Encoding) (s : MachineState) : Prop :=
  s.pc = addr idxChains ∧ s.getReg .x8 = s0.getReg .x8 ∧
  (∀ j : ChainIndex, s.getMem (DIGITS + BitVec.ofNat 64 (8 * j.val)) = BitVec.ofNat 64 (enc j).val) ∧
  Frame WDecode s0 s

def DecodePost (H : HashInput → HashOutput) (s0 : MachineState) (d : BitVec 128) (s : MachineState) :
    Prop :=
  (∀ enc, TargetSum.decodeDigest d = some enc → DecodeAccept s0 enc s) ∧
  (TargetSum.decodeDigest d = none → Rejected H s0 s)

/-- The loop invariant after `k` of the 21 iterations. -/
def DecodeInv (s0 : MachineState) (d : BitVec 128) (k : Nat) (s : MachineState) : Prop :=
  s.code = s0.code ∧ s.pc = (if k < 21 then addr idxDecodeLoop else addr idxDecodePost) ∧
  s.getReg .x6 = dLo d >>> (3 * k) ∧ s.getReg .x7 = dHi d >>> (3 * k) ∧
  s.getReg .x22 = BitVec.ofNat 64 (sumTo d k) ∧ s.getReg .x23 = DIGITS + BitVec.ofNat 64 (8 * k) ∧
  s.getReg .x24 = DIGITS + 168 ∧ s.getReg .x8 = s0.getReg .x8 ∧
  (∀ j, j < k → s.getMem (DIGITS + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 (dig d j) ∧
    s.getMem (DIGITS + 168#64 + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 (dig d (21 + j))) ∧
  Frame WDecode s0 s

set_option maxRecDepth 4000 in
theorem decode_body (s0 : MachineState) (hC : CodeAt s0.code (addr idxDecode) decode 0)
    (d : BitVec 128) (k : Nat) (hk : k < 21) (s : MachineState) (hI : DecodeInv s0 d k s) :
    Runs H s (DecodeInv s0 d (k + 1)) := by
  obtain ⟨hcode, hpc, h6, h7, h22, h23, h24, h8, hD, hfr⟩ := hI
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  rw [if_pos hk] at hpc
  sym_norm at hcode hpc h6 h7 h22 h23 h24 h8 hD
  subst hpc
  rw [← hcode] at hC
  sym_code hC [decode, decodePre, decodeLoop, decodePost, haltWith] [decodeBody]
  obtain ⟨-, -, -, -, -, -, -, -, -, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, -⟩ := hC
  sym_plain_f f9
  simp only [h6, digit_lo d k hk]
  sym_sd_f_with f10 (by sym_norm; rw [h23]; sym_valid_off)
  sym_plain_f f11
  sym_plain_f f12
  simp only [h7, digit_hi d k hk]
  sym_sd_f_with f13 (by sym_norm; rw [h23]; sym_valid_off)
  sym_plain_f f14; sym_plain_f f15; sym_plain_f f16; sym_plain_f f17
  simp only [h6, h7, h22, h23, sumTo_succ_word, shr3]
  have hx23 : 66944#64 + BitVec.ofNat 64 (8 * k) + 8#64 = 66944#64 + BitVec.ofNat 64 (8 * (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [hx23]
  sym_plain_f f18
  simp only [h24]
  have hD' : ∀ j, j < k + 1 →
      (if 66944#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k) + 168#64 then
          BitVec.ofNat 64 (dig d (21 + k))
        else if 66944#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k) then
          BitVec.ofNat 64 (dig d k)
        else M (66944#64 + BitVec.ofNat 64 (8 * j))) = BitVec.ofNat 64 (dig d j) ∧
      (if 67112#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k) + 168#64 then
          BitVec.ofNat 64 (dig d (21 + k))
        else if 67112#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k) then
          BitVec.ofNat 64 (dig d k)
        else M (67112#64 + BitVec.ofNat 64 (8 * j))) = BitVec.ofNat 64 (dig d (21 + j)) := by
    intro j hj
    have t1 : ¬ (66944#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k) + 168#64) := by addr_ne
    have t2 : ¬ (67112#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k)) := by addr_ne
    simp only [t1, t2, ↓reduceIte]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · have t3 : ¬ (66944#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k)) := by addr_ne
      have t4 : ¬ (67112#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * k) + 168#64) := by
        addr_ne
      simp only [t3, t4, ↓reduceIte]
      exact hD j hjk
    · have hjk' : j = k := by omega
      subst hjk'
      have t4 : 67112#64 + BitVec.ofNat 64 (8 * j) = 66944#64 + BitVec.ofNat 64 (8 * j) + 168#64 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp only [t4, ↓reduceIte]
      exact ⟨trivial, trivial⟩
  have hFr : ∀ a, ¬ WDecode a →
      (if a = 66944#64 + BitVec.ofNat 64 (8 * k) + 168#64 then BitVec.ofNat 64 (dig d (21 + k))
        else if a = 66944#64 + BitVec.ofNat 64 (8 * k) then BitVec.ofNat 64 (dig d k) else M a) = M a := by
    intro a ha
    simp only [WDecode, InRange] at ha
    sym_norm at ha
    have t1 : ¬ (a = 66944#64 + BitVec.ofNat 64 (8 * k) + 168#64) := by addr_ne
    have t2 : ¬ (a = 66944#64 + BitVec.ofNat 64 (8 * k)) := by addr_ne
    simp only [t1, t2, ↓reduceIte]
  rcases Nat.lt_or_ge (k + 1) 21 with hlt | hge
  · have hne : ¬ (66944#64 + BitVec.ofNat 64 (8 * (k + 1)) = 67112#64) := by addr_ne
    simp only [hne, not_false_eq_true, ↓reduceIte]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_norm; rw [if_pos hlt]
    · sym_norm
    · sym_norm
    · sym_norm
    · sym_norm
    · sym_norm; exact h24
    · sym_norm; exact h8
    · intro j hj; sym_norm; exact hD' j hj
    · refine Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro a ha; sym_norm; exact hFr a ha
      · sym_frame_reg
  · have heq : 66944#64 + BitVec.ofNat 64 (8 * (k + 1)) = 67112#64 := by
      rw [show k + 1 = 21 by omega]; rfl
    simp only [heq, not_true_eq_false, ↓reduceIte]
    refine Runs.done ⟨hcode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_norm; rw [if_neg (by omega)]
    · sym_norm
    · sym_norm
    · sym_norm
    · sym_norm; exact heq.symm
    · sym_norm; exact h24
    · sym_norm; exact h8
    · intro j hj; sym_norm; exact hD' j hj
    · refine Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro a ha; sym_norm; exact hFr a ha
      · sym_frame_reg

theorem decode_exit (H : HashInput → HashOutput) (s0 : MachineState)
    (hC : CodeAt s0.code (addr idxDecode) decode 0) (d : BitVec 128)
    (h63 : d.getLsbD 63 = false) (h127 : d.getLsbD 127 = false) (s : MachineState)
    (hI : DecodeInv s0 d 21 s) : Runs H s (DecodePost H s0 d) := by
  obtain ⟨hcode, hpc, -, -, h22, -, -, h8, hD, hfr⟩ := hI
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  rw [if_neg (by decide)] at hpc
  sym_norm at hcode hpc h22 h8 hD
  subst hpc
  rw [← hcode] at hC
  sym_code hC [decode, decodePre, decodeLoop, decodePost, haltWith] [decodeBody]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f19, f20, f21, f22, f23, f24, -⟩ := hC
  have hle := sumTo_le d 21
  sym_plain_f f19
  sym_plain_f f20
  simp only [h22]
  by_cases hsum : sumTo d 21 = 195
  · have heq : BitVec.ofNat 64 (sumTo d 21) = 195#64 := by rw [hsum]
    simp only [heq, not_true_eq_false, ↓reduceIte]
    sym_plain_f f21
    refine Runs.done ⟨?_, ?_⟩
    · intro enc henc
      have henc' : some (TargetSum.digestEncoding d) = some enc :=
        (decodeDigest_some d h63 h127 hsum).symm.trans henc
      obtain rfl := Option.some.inj henc'
      refine ⟨?_, ?_, ?_, ?_⟩
      · sym_norm
      · sym_norm; exact h8
      · intro j
        rw [digestEncoding_val]
        have hj42 : j.val < 42 := j.isLt
        rcases Nat.lt_or_ge j.val 21 with hj21 | hj21
        · sym_norm; exact (hD j.val hj21).1
        · have hD2 := (hD (j.val - 21) (by omega)).2
          have haddr : 67112#64 + BitVec.ofNat 64 (8 * (j.val - 21)) =
              66944#64 + BitVec.ofNat 64 (8 * j.val) := by
            apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          rw [haddr, show 21 + (j.val - 21) = j.val by omega] at hD2
          sym_norm; exact hD2
      · exact Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩
    · intro hnone
      exact absurd ((decodeDigest_some d h63 h127 hsum).symm.trans hnone) (Option.some_ne_none _)
  · have hne : ¬ (BitVec.ofNat 64 (sumTo d 21) = 195#64) := by
      intro h; apply hsum
      have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    simp only [hne, not_false_eq_true, ↓reduceIte]
    sym_plain_f f22; sym_plain_f f23
    refine Runs.done ⟨?_, ?_⟩
    · intro enc henc
      exact absurd ((decodeDigest_none_sum d hsum).symm.trans henc) (Option.some_ne_none _).symm
    · intro _
      exact ⟨⟨f24, by sym_norm⟩, stepH_halt f24 (by sym_norm), by sym_norm,
        Frame.trans hfr ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩⟩

/-- The decode region against `decodeDigest`. -/
theorem decode_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxDecode) decode 0) (d : BitVec 128)
    (hpc : s.pc = addr idxDecode) (h20 : s.getReg .x20 = dLo d) (h21 : s.getReg .x21 = dHi d) :
    Runs H s (DecodePost H s d) := by
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  sym_norm at hpc h20 h21
  subst hpc
  have hC' := hC
  sym_code hC' [decode, decodePre, decodeLoop, decodePost, haltWith] [decodeBody]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, -, -, -, -, -, -, -, -, -, -, -, -, -, f22, f23, f24, -⟩ := hC'
  sym_plain_f f0
  simp only [h20]
  sym_plain_f f1
  by_cases h63 : d.getLsbD 63 = false
  · have hz : dLo d >>> 63 = 0#64 := (pad63 d).mpr h63
    simp only [hz, not_true_eq_false, ↓reduceIte]
    sym_plain_f f2
    simp only [h21]
    sym_plain_f f3
    by_cases h127 : d.getLsbD 127 = false
    · have hz' : dHi d >>> 63 = 0#64 := (pad127 d).mpr h127
      simp only [hz', not_true_eq_false, ↓reduceIte]
      sym_plain_f f4; sym_plain_f f5; sym_plain_f f6; sym_plain_f f7; sym_plain_f f8
      simp only [h20, h21]
      refine Runs.bind (Runs.loop 21 (fun k s' hk hI => decode_body _ hC d k hk s' hI) _ ?_)
        (fun s2 hI => decode_exit H _ hC d h63 h127 s2 hI)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sym_norm
      · sym_norm; rw [BitVec.ushiftRight_zero]
      · sym_norm; rw [BitVec.ushiftRight_zero]
      · sym_norm; rfl
      · sym_norm
      · sym_norm
      · sym_norm
      · intro j hj; exact absurd hj (Nat.not_lt_zero _)
      · exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩
    · have hnz : ¬ (dHi d >>> 63 = 0#64) := fun h => h127 ((pad127 d).mp h)
      simp only [hnz, not_false_eq_true, ↓reduceIte]
      sym_plain_f f22; sym_plain_f f23
      refine Runs.done ⟨?_, ?_⟩
      · intro enc henc
        exact absurd ((decodeDigest_none_127 d h127).symm.trans henc) (Option.some_ne_none _).symm
      · intro _
        exact ⟨⟨f24, by sym_norm⟩, stepH_halt f24 (by sym_norm), by sym_norm,
          ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩⟩
  · have hnz : ¬ (dLo d >>> 63 = 0#64) := fun h => h63 ((pad63 d).mp h)
    simp only [hnz, not_false_eq_true, ↓reduceIte]
    sym_plain_f f22; sym_plain_f f23
    refine Runs.done ⟨?_, ?_⟩
    · intro enc henc
      exact absurd ((decodeDigest_none_63 d h63).symm.trans henc) (Option.some_ne_none _).symm
    · intro _
      exact ⟨⟨f24, by sym_norm⟩, stepH_halt f24 (by sym_norm), by sym_norm,
        ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩⟩

end XmssAsm
