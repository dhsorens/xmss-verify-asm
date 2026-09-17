/-
  XmssAsm.Machine.Hash

  The abstract hash oracle as a `Decomp.Stepper`, and the forward-execution
  vocabulary (`Reaches`, `Runs`) every region contract is stated in.

  ## The hash-call boundary (`HashContract H`)

  The verifier is parametric in the hash `H : List UInt8 → BitVec 256`. The
  RV code reaches `H` through one host-neutral convention:

      x5 (t0)  = HASH_ID
      x10 (a0) = byte address of the input
      x11 (a1) = input length in bytes
      x12 (a2) = byte address of the 32-byte output, 8-aligned
      ECALL

  Effect (`hashEffect`): the 32 output bytes `H(mem[a0 .. a0+a1))` are written
  at `a2` as four little-endian doublewords (`outWords`), the pc advances by 4,
  and nothing else changes -- no register, no other memory, no code. The call
  traps (`none`) when the input range or the output doublewords are not valid
  machine memory (`hashArgsValid`), exactly as an ordinary load or store would.

  Everything that is not this one `ECALL` shape is `RiscvZkvm.Rv64.step`
  unchanged (`stepH_of_step`), so ordinary instructions keep their ordinary
  RV64 semantics and the only assumption the correctness theorem makes beyond
  the machine model is the semantic contract above. No SP1, ZisK, BLAKE2s or
  host ABI appears here.

  Benchmark cost is not part of the semantics; `XmssAsm.Machine.Eval` charges a
  documented constant per hash call.
-/

module

public import XmssAsm.Upstream

@[expose] public section

namespace XmssAsm

open RiscvZkvm.Rv64

/-- The syscall id of the abstract hash call, in `x5`. Distinct from the four
    host ids `step` interprets (`0`, `0x02`, `0x10`, `0xF2`). -/
def HASH_ID : Word := 0x48415348

/-- The 32-byte hash output as four little-endian doublewords. -/
def outWords (o : BitVec 256) : List Word :=
  [o.extractLsb' 0 64, o.extractLsb' 64 64, o.extractLsb' 128 64, o.extractLsb' 192 64]

/-- The input bytes of a hash call, read from `a0` for `a1` bytes. -/
def hashInputOf (s : MachineState) : List UInt8 :=
  (s.readBytes (s.getReg .x10) (s.getReg .x11).toNat).map UInt8.ofBitVec

/-- The output block `a2 .. a2 + 32` is four valid doubleword cells. -/
def outBlockValid (a : Word) : Bool :=
  isValidDwordAccess a && isValidDwordAccess (a + 8) &&
  isValidDwordAccess (a + 16) && isValidDwordAccess (a + 24)

/-- A hash call is admitted when its input range and output block are valid
    memory. -/
def hashArgsValid (s : MachineState) : Bool :=
  isValidOutputRange (s.getReg .x10) (s.getReg .x11).toNat && outBlockValid (s.getReg .x12)

/-- The effect of one hash call: write `H(input)` at `a2`, advance the pc. -/
def hashEffect (H : List UInt8 → BitVec 256) (s : MachineState) : MachineState :=
  (s.writeWords (s.getReg .x12) (outWords (H (hashInputOf s)))).setPC (s.pc + 4)

/-- `hashEffect` with the hash output named: the four output stores at
    literal offsets, the shape symbolic execution keeps. -/
def hashEffectWith (o : BitVec 256) (s : MachineState) : MachineState :=
  ((((s.setMem (s.getReg .x12) (o.extractLsb' 0 64)).setMem
    (s.getReg .x12 + 8) (o.extractLsb' 64 64)).setMem
    (s.getReg .x12 + 8 + 8) (o.extractLsb' 128 64)).setMem
    (s.getReg .x12 + 8 + 8 + 8) (o.extractLsb' 192 64)).setPC (s.pc + 4)

theorem hashEffect_eq_with (H : List UInt8 → BitVec 256) (s : MachineState) :
    hashEffect H s = hashEffectWith (H (hashInputOf s)) s := rfl

/-- The machine is at a hash call. -/
def AtHashCall (s : MachineState) : Prop :=
  s.code s.pc = some .ECALL ∧ s.getReg .x5 = HASH_ID

/-- One step of the RV64 machine extended with the hash oracle `H`. -/
def stepH (H : List UInt8 → BitVec 256) (s : MachineState) : Option MachineState :=
  match s.code s.pc with
  | some .ECALL =>
    if s.getReg .x5 = HASH_ID then
      if hashArgsValid s then some (hashEffect H s) else none
    else step s
  | _ => step s

theorem code_hashEffect {H : List UInt8 → BitVec 256} {s : MachineState} :
    (hashEffect H s).code = s.code := by
  simp [hashEffect]

theorem stepH_of_step {H : List UInt8 → BitVec 256} {s : MachineState}
    (h : ¬ AtHashCall s) : stepH H s = step s := by
  unfold stepH
  split
  · rename_i heq
    by_cases h5 : s.getReg .x5 = HASH_ID
    · exact absurd ⟨heq, h5⟩ h
    · simp [h5]
  · rfl

theorem code_stepH {H : List UInt8 → BitVec 256} {s s' : MachineState}
    (h : stepH H s = some s') : s'.code = s.code := by
  by_cases hc : AtHashCall s
  · unfold stepH at h
    obtain ⟨hf, h5⟩ := hc
    rw [hf] at h
    simp only [h5, if_true] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact code_hashEffect
    · simp at h
  · rw [stepH_of_step hc] at h; exact code_step h

/-- The hash-oracle machine as a `Decomp.Stepper`. -/
def hashStepper (H : List UInt8 → BitVec 256) : Decomp.Stepper where
  next := stepH H
  code_next := code_stepH
  inv _ := True
  inv_next _ _ := trivial

@[simp] theorem hashStepper_next (H : List UInt8 → BitVec 256) :
    (hashStepper H).next = stepH H := rfl

/-! ## Step lemmas, one per instruction class the verifier uses -/

theorem stepH_plain {H : List UInt8 → BitVec 256} {s : MachineState} {i : Instr}
    (hf : s.code s.pc = some i) (hm : i.isMemAccess = false)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK) :
    stepH H s = some (execInstrBr s i) := by
  rw [stepH_of_step (fun hc => he (Option.some.inj (hf.symm.trans hc.1)))]
  exact step_non_ecall_non_mem hf he hb hm

theorem stepH_ld {H : List UInt8 → BitVec 256} {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hf : s.code s.pc = some (.LD rd rs1 off))
    (hv : isValidDwordAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepH H s = some (execInstrBr s (.LD rd rs1 off)) := by
  rw [stepH_of_step (fun hc => by
    obtain ⟨h1, _⟩ := hc; rw [hf] at h1; exact Instr.noConfusion (Option.some.inj h1))]
  exact step_ld hf hv

theorem stepH_sd {H : List UInt8 → BitVec 256} {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hf : s.code s.pc = some (.SD rs1 rs2 off))
    (hv : isValidDwordAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepH H s = some (execInstrBr s (.SD rs1 rs2 off)) := by
  rw [stepH_of_step (fun hc => by
    obtain ⟨h1, _⟩ := hc; rw [hf] at h1; exact Instr.noConfusion (Option.some.inj h1))]
  exact step_sd hf hv

theorem stepH_hash {H : List UInt8 → BitVec 256} {s : MachineState}
    (hf : s.code s.pc = some .ECALL) (h5 : s.getReg .x5 = HASH_ID)
    (hv : hashArgsValid s = true) :
    stepH H s = some (hashEffect H s) := by
  unfold stepH; rw [hf]; simp [h5, hv]

/-- The hash call with its input identified: the successor mentions `H inp`
    rather than `H (hashInputOf s)`. -/
theorem stepH_hash_input {H : List UInt8 → BitVec 256} {s : MachineState} {inp : List UInt8}
    (hf : s.code s.pc = some .ECALL) (h5 : s.getReg .x5 = HASH_ID)
    (hv : hashArgsValid s = true) (hin : hashInputOf s = inp) :
    stepH H s = some (hashEffectWith (H inp) s) := by
  rw [stepH_hash hf h5 hv, hashEffect_eq_with, hin]

/-- `HALT`: `ECALL` with `x5 = 0` stops the machine. -/
theorem stepH_halt {H : List UInt8 → BitVec 256} {s : MachineState}
    (hf : s.code s.pc = some .ECALL) (h5 : s.getReg .x5 = 0) :
    stepH H s = none := by
  have hne : s.getReg .x5 ≠ HASH_ID := by rw [h5]; decide
  unfold stepH; rw [hf]; simp only [hne, if_false]
  exact step_ecall_halt hf h5

/-! ## Forward execution -/

/-- `s'` is reachable from `s` in finitely many steps. -/
def Reaches (H : List UInt8 → BitVec 256) (s s' : MachineState) : Prop :=
  ∃ k, (hashStepper H).iter k s = some s'

/-- From `s`, execution reaches some state satisfying `Q`. Every region
    contract is a `Runs`; termination is built in. -/
def Runs (H : List UInt8 → BitVec 256) (s : MachineState) (Q : MachineState → Prop) : Prop :=
  ∃ s', Reaches H s s' ∧ Q s'

namespace Reaches

variable {H : List UInt8 → BitVec 256}

theorem refl (s : MachineState) : Reaches H s s := ⟨0, rfl⟩

theorem step {s s1 s' : MachineState} (h : stepH H s = some s1) (h2 : Reaches H s1 s') :
    Reaches H s s' := by
  obtain ⟨k, hk⟩ := h2
  exact ⟨k + 1, by simp [Decomp.Stepper.iter_succ, h, hk]⟩

theorem trans {s s1 s' : MachineState} (h1 : Reaches H s s1) (h2 : Reaches H s1 s') :
    Reaches H s s' := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k1 + k2, Decomp.Stepper.iter_add_eq hk1 hk2⟩

theorem code_eq {s s' : MachineState} (h : Reaches H s s') : s'.code = s.code := by
  obtain ⟨k, hk⟩ := h
  exact Decomp.Stepper.code_iter hk

end Reaches

namespace Runs

variable {H : List UInt8 → BitVec 256}

theorem done {s : MachineState} {Q : MachineState → Prop} (h : Q s) : Runs H s Q :=
  ⟨s, Reaches.refl s, h⟩

theorem step {s s1 : MachineState} {Q : MachineState → Prop}
    (h : stepH H s = some s1) (h2 : Runs H s1 Q) : Runs H s Q := by
  obtain ⟨s', hr, hq⟩ := h2
  exact ⟨s', Reaches.step h hr, hq⟩

theorem mono {s : MachineState} {Q Q' : MachineState → Prop}
    (h : Runs H s Q) (hQ : ∀ s', Q s' → Q' s') : Runs H s Q' := by
  obtain ⟨s', hr, hq⟩ := h
  exact ⟨s', hr, hQ s' hq⟩

/-- Sequential composition of contracts. -/
theorem bind {s : MachineState} {Q R : MachineState → Prop}
    (h : Runs H s Q) (h2 : ∀ s', Q s' → Runs H s' R) : Runs H s R := by
  obtain ⟨s1, hr1, hq⟩ := h
  obtain ⟨s2, hr2, hR⟩ := h2 s1 hq
  exact ⟨s2, Reaches.trans hr1 hr2, hR⟩

theorem of_reaches {s s' : MachineState} {Q : MachineState → Prop}
    (h : Reaches H s s') (hq : Q s') : Runs H s Q := ⟨s', h, hq⟩

/-- Bounded iteration: an invariant indexed by an iteration counter, whose body
    is a contract from `Inv i` to `Inv (i+1)`, runs from `Inv 0` to `Inv n`.
    This is how the 21-, 32-, 42- and (7 - x)-fold loops are proved: the body
    is proved once, the count is eliminated by induction. -/
theorem loop {Inv : Nat → MachineState → Prop} (n : Nat)
    (hbody : ∀ i s, i < n → Inv i s → Runs H s (Inv (i + 1))) :
    ∀ s, Inv 0 s → Runs H s (Inv n) := by
  suffices h : ∀ m, ∀ i s, i + m = n → Inv i s → Runs H s (Inv n) by
    intro s h0; exact h n 0 s (by omega) h0
  intro m
  induction m with
  | zero => intro i s hi hInv; subst hi; exact done (by simpa using hInv)
  | succ m ih =>
    intro i s hi hInv
    exact bind (hbody i s (by omega) hInv) (fun s' h' => ih (i + 1) s' (by omega) h')

end Runs

end XmssAsm
