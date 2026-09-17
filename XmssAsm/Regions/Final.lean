/-
  XmssAsm.Regions.Final

  The final region: compare `CUR` with `ROOT` and halt with `a0 = 1` on
  equality, `a0 = 0` otherwise. Writes nothing. LEGACY file.
-/

import XmssAsm.Regions.Common
import XmssAsm.Contract

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- The verifier halted with the given result and no memory written. -/
def Halted (H : HashInput → HashOutput) (s0 : MachineState) (b : Bool) (s : MachineState) : Prop :=
  Decomp.SyscallHalted s ∧ stepH H s = none ∧ s.getReg .x10 = resultWord b ∧
  Frame (fun _ => False) s0 s

theorem final_correct (H : HashInput → HashOutput) (s : MachineState)
    (hC : CodeAt s.code (addr idxFinal) final 0) (r root : Digest) (hpc : s.pc = addr idxFinal)
    (hcur : HasDigest s CUR r) (hroot : HasDigest s ROOT root) :
    Runs H s (Halted H s (decide (r = root))) := by
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  simp only [HasDigest] at hcur hroot
  sym_norm at hpc hcur hroot
  subst hpc
  sym_code1 hC [final, haltWith]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, -⟩ := hC
  sym_plain_f f0; sym_ld_f f1; sym_ld_f f2; sym_plain_f f3; sym_ld_f f4; sym_ld_f f5
  sym_plain_f f6
  simp only [hcur.1, hroot.1]
  by_cases h1 : dLo r = dLo root
  · simp only [h1, not_true_eq_false, ↓reduceIte]
    sym_plain_f f7
    simp only [hcur.2, hroot.2]
    by_cases h2 : dHi r = dHi root
    · simp only [h2, not_true_eq_false, ↓reduceIte]
      have hr : r = root := (digest_eq_iff r root).mpr ⟨h1, h2⟩
      sym_plain_f f8; sym_plain_f f9
      refine Runs.done ⟨⟨f10, by sym_norm⟩, stepH_halt f10 (by sym_norm), ?_,
        ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩⟩
      sym_norm; simp [resultWord, hr]
    · simp only [h2, not_false_eq_true, ↓reduceIte]
      have hr : ¬ r = root := fun h => h2 ((digest_eq_iff r root).mp h).2
      sym_plain_f f11; sym_plain_f f12
      refine Runs.done ⟨⟨f13, by sym_norm⟩, stepH_halt f13 (by sym_norm), ?_,
        ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩⟩
      sym_norm; simp [resultWord, hr]
  · simp only [h1, not_false_eq_true, ↓reduceIte]
    have hr : ¬ r = root := fun h => h1 ((digest_eq_iff r root).mp h).1
    sym_plain_f f11; sym_plain_f f12
    refine Runs.done ⟨⟨f13, by sym_norm⟩, stepH_halt f13 (by sym_norm), ?_,
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by sym_frame_reg⟩⟩
    sym_norm; simp [resultWord, hr]

end XmssAsm
