/-
  XmssAsm.Regions.Init

  The `init` region: copy `P` into both hash buffers, lay out the encoding
  payload `m ‖ ρ ‖ 0^8`, load the epoch, write the encoding tweak, hash, and
  load the encoding digest into `x20`/`x21`. LEGACY file.
-/

import XmssAsm.Regions.Common
import XmssAsm.Represent

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- The write set of `init`: `BUFA` through the payload, `BUFL_P`, and `OUT`. -/
def WInit (a : Word) : Prop := InRange BUFA 96 a ∨ InRange BUFL_P 16 a ∨ InRange OUT 32 a

def InitPost (H : HashInput → HashOutput) (s0 : MachineState) (P : PublicParameter) (ep : Epoch)
    (msg : Message) (rho : Randomness) (s : MachineState) : Prop :=
  s.pc = addr idxDecode ∧ s.getReg .x8 = BitVec.ofNat 64 ep.val ∧
  s.getReg .x20 = dLo (encD H P ep msg rho) ∧ s.getReg .x21 = dHi (encD H P ep msg rho) ∧
  HasDigest s BUFA_P P ∧ HasDigest s BUFL_P P ∧ Frame WInit s0 s

set_option maxRecDepth 4000 in
theorem init_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code CODE_BASE init 0) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) (hpc : s.pc = CODE_BASE) (hrep : Represents s pk ep msg sig) :
    Runs H s (InitPost H s pk.parameter ep msg sig.randomness) := by
  obtain ⟨-, hP, hep, hmsg, hrho, -, -⟩ := hrep
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest, HasMessage, HasRandomness] at hP hmsg hrho
  sym_norm at hpc hP hep hmsg hrho
  subst hpc
  sym_code1 hC [init, initP, initPayload, initHash]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38,
    f39, f40, f41, f42, -⟩ := hC
  sym_plain_f f0; sym_ld_f f1; sym_ld_f f2; sym_plain_f f3; sym_sd_f f4; sym_sd_f f5
  sym_plain_f f6; sym_sd_f f7; sym_sd_f f8
  sym_plain_f f9; sym_ld_f f10; sym_ld_f f11; sym_ld_f f12; sym_ld_f f13
  sym_plain_f f14; sym_sd_f f15; sym_sd_f f16; sym_sd_f f17; sym_sd_f f18
  sym_plain_f f19; sym_ld_f f20; sym_ld_f f21; sym_ld_f f22
  sym_plain_f f23; sym_sd_f f24; sym_sd_f f25; sym_sd_f f26; sym_sd_f f27
  sym_plain_f f28; sym_ld_f f29; sym_plain_f f30; sym_plain_f f31; sym_sd_f f32
  sym_plain_f f33; sym_sd_f f34
  sym_plain_f f35; sym_plain_f f36; sym_plain_f f37; sym_plain_f f38
  sym_hash_in_f f39 (wordsBytes [tw0 4 0, tw1 ep.val, dLo pk.parameter, dHi pk.parameter,
    mW msg 0, mW msg 1, mW msg 2, mW msg 3, rW sig.randomness 0, rW sig.randomness 1,
    rW sig.randomness 2, 0])
  case hin =>
    rw [hashInputOf_eq _ 12 (by sym_norm) (by sym_norm) (by sym_norm)]
    simp only [MachineState.readWords_succ, MachineState.readWords_zero]
    sym_norm
    simp only [hP.1, hP.2, hep, hmsg.1, hmsg.2.1, hmsg.2.2.1, hmsg.2.2.2, hrho.1, hrho.2.1, hrho.2.2,
      tw0_encoding, tw1_machine]
  sym_plain_f f40; sym_ld_f f41; sym_ld_f f42
  refine Runs.done ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_norm
  · sym_norm; exact hep
  · sym_norm; rw [encD_eq, dLo_truncateHash]; rfl
  · sym_norm; rw [encD_eq, dHi_truncateHash]; rfl
  · simp only [HasDigest]; sym_norm; exact hP
  · simp only [HasDigest]; sym_norm; exact hP
  · sym_frame_W WInit

end XmssAsm
