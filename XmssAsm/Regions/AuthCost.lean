/-
  XmssAsm.Regions.AuthCost

  The step cost of the authentication-path region, as a theorem.

  `XmssAsm.Regions.Auth` proves what the 32 merkle levels *compute*; this file
  proves how many machine steps they *take*. Both walk the same instructions
  with the same tactics, over different relations: `Runs` there, `RunsN` here
  (`XmssAsm.Machine.Cost`), so the step count is part of the statement rather
  than hidden behind an existential.

  The cost is data-dependent in exactly one place. `authSelect` branches on bit
  `L` of the epoch to order the two children in the hash payload: a clear bit
  falls through to two stores, a set bit takes four stores and a `JAL`. So a
  level costs 34 steps when the bit is clear and 37 when it is set, and the
  region costs

      auth_steps ep = 2 + 32 * 34 + 3 * popcount32 ep = 1090 + 3 * popcount32 ep

  maximised, uniquely, at `ep = 2 ^ 32 - 1` (`authSteps_lt_of_ne`). That is why
  the benchmark's worst-case accepting fixture is `valid-epmax`: the worst case
  follows from the program, so the secondary score is a real bound rather than
  the largest number the corpus happens to contain.

  The invariant here is deliberately weaker than `AuthInv`: it pins the code,
  the pc and the three registers the control flow reads (`x8`, `x25`, `x26`),
  and says nothing about memory, because nothing the cost depends on lives
  there.
-/

module

public import XmssAsm.Machine.Sym

@[expose] public section

namespace XmssAsm

open RiscvZkvm.Rv64

/-! ## Population count

`popcount32` is written as a `costSum` so that it composes directly with
`RunsN.loopSum`, whose cost argument is a function of the loop index. -/

/-- The number of one bits among the low 32 bits of `x`. -/
def popcount32 (x : Nat) : Nat := costSum (fun i => if x.testBit i then 1 else 0) 32

theorem popcount32_le_aux (x n : Nat) :
    costSum (fun i => if x.testBit i then 1 else 0) n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih => rw [costSum_succ]; exact Nat.add_le_add ih (by split <;> omega)

theorem popcount32_le (x : Nat) : popcount32 x ≤ 32 := popcount32_le_aux x 32

theorem popcount32_max : popcount32 (2 ^ 32 - 1) = 32 := by decide

/-- If some bit below `n` is clear then fewer than `n` of them are set. -/
theorem popcount_lt_of_bit_clear (x j : Nat) (hbit : x.testBit j = false) :
    ∀ n, j < n → costSum (fun i => if x.testBit i then 1 else 0) n < n := by
  intro n hjn
  induction n with
  | zero => omega
  | succ k ih =>
    rw [costSum_succ]
    rcases Nat.lt_or_ge j k with hlt | hge
    · have h1 := ih hlt
      have h2 : (if x.testBit k then 1 else 0) ≤ 1 := by split <;> omega
      omega
    · have hjk : j = k := by omega
      subst hjk
      have hle := popcount32_le_aux x j
      simp only [hbit, Bool.false_eq_true, if_false]
      omega

/-- The all-ones epoch is the *unique* maximiser: every other 32-bit epoch has
    strictly fewer set bits, hence a strictly cheaper authentication path. -/
theorem popcount32_lt_of_ne (x : Nat) (hx : x < 2 ^ 32) (hne : x ≠ 2 ^ 32 - 1) :
    popcount32 x < 32 := by
  obtain ⟨j, hj, hbit⟩ : ∃ j, j < 32 ∧ x.testBit j = false := by
    refine Classical.byContradiction fun h => ?_
    have hall : ∀ i, i < 32 → x.testBit i = true := by
      intro i hi
      cases hb : x.testBit i with
      | false => exact absurd ⟨i, hi, hb⟩ h
      | true => rfl
    refine hne (Nat.eq_of_testBit_eq fun i => ?_)
    rcases Nat.lt_or_ge i 32 with hi | hi
    · rw [hall i hi, Nat.testBit_two_pow_sub_one, decide_eq_true hi]
    · have hxi : x < 2 ^ i := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi)
      rw [Nat.testBit_lt_two_pow hxi, Nat.testBit_two_pow_sub_one,
        decide_eq_false (by omega : ¬ i < 32)]
  simpa only [popcount32] using popcount_lt_of_bit_clear x j hbit 32 hj

/-! ## Arithmetic on the level counter -/

theorem cost_shamt (L : Nat) (hL : L < 64) : (BitVec.ofNat 64 L).toNat % 64 = L := by
  simp only [BitVec.toNat_ofNat]; omega

theorem cost_ofNat_succ (L : Nat) : BitVec.ofNat 64 L + 1#64 = BitVec.ofNat 64 (L + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem cost_ptr_succ (base : Word) (L : Nat) :
    base + BitVec.ofNat 64 (16 * L) + 16#64 = base + BitVec.ofNat 64 (16 * (L + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem cost_bit_test (ep L : Nat) (hep : ep < 2 ^ 32) :
    ((BitVec.ofNat 64 ep >>> L) &&& 1#64 = 0#64) ↔ ep.testBit L = false := by
  rw [BitVec.toNat_eq]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not,
    Nat.reducePow, Nat.reduceMod]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (a := ep) (by omega)]
  omega

/-! ## The cost invariant -/

/-- The cost of one merkle level: 34 steps, plus 3 more when bit `L` of the
    epoch is set and `authSelect` takes its long arm. -/
def authLevelCost (ep L : Nat) : Nat := 34 + 3 * (if ep.testBit L then 1 else 0)

/-- What the auth loop's control flow reads, and nothing else: the loaded
    program, the pc at the loop head, the epoch in `x8`, the level counter in
    `x25`, the sibling pointer in `x26`. -/
def AuthCostInv (ep L : Nat) (s : MachineState) : Prop :=
  s.code = verifierCode ∧ s.pc = (if L < 32 then addr idxAuthLoop else addr idxFinal) ∧
  s.getReg .x8 = BitVec.ofNat 64 ep ∧ s.getReg .x25 = BitVec.ofNat 64 L ∧
  s.getReg .x26 = AUTH + BitVec.ofNat 64 (16 * L)

/-- The state at the loop's `BNE`, after `authHash` has advanced the counters. -/
def AuthCostTail (ep L : Nat) (s : MachineState) : Prop :=
  s.code = verifierCode ∧ s.pc = addr (idxAuthHash + 23) ∧
  s.getReg .x8 = BitVec.ofNat 64 ep ∧ s.getReg .x25 = BitVec.ofNat 64 (L + 1) ∧
  s.getReg .x26 = AUTH + BitVec.ofNat 64 (16 * (L + 1)) ∧ s.getReg .x6 = 32#64

/-- The loop's back edge: one `BNE`, to the invariant at `L + 1`. -/
theorem authCost_tail {H : List UInt8 → BitVec 256} (ep L : Nat) (hL : L < 32) (s : MachineState)
    (h : AuthCostTail ep L s) : RunsN H s 1 (AuthCostInv ep (L + 1)) := by
  obtain ⟨hcode, hpc, h8, h25, h26, h6⟩ := h
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  sym_norm at hcode hpc h8 h25 h26 h6
  subst hpc
  have hC : CodeAt C (addr idxAuth) auth 0 := by rw [hcode]; exact verifierCode_auth
  sym_code hC [auth, authPre, authLoop] [authBody, authSelect, authHash]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, f40, -⟩ := hC
  symc_plain f40
  rcases Nat.lt_or_ge (L + 1) 32 with hlt | hge
  · have hne : ¬ (BitVec.ofNat 64 (L + 1) = 32#64) := by
      intro hh; have := congrArg BitVec.toNat hh
      simp only [BitVec.toNat_ofNat] at this; omega
    rw [h25, h6]
    simp only [hne, not_false_eq_true, ↓reduceIte]
    exact RunsN.done ⟨hcode, by sym_norm; rw [if_pos hlt], by sym_norm; exact h8,
      by sym_norm; exact h25, by sym_norm; exact h26⟩
  · have heq : BitVec.ofNat 64 (L + 1) = 32#64 := by rw [show L + 1 = 32 by omega]
    rw [h25, h6]
    simp only [heq, not_true_eq_false, ↓reduceIte]
    exact RunsN.done ⟨hcode, by sym_norm; rw [if_neg (by omega)], by sym_norm; exact h8,
      by sym_norm; exact h25, by sym_norm; exact h26⟩

set_option maxRecDepth 8000 in
/-- One merkle level, at its exact step cost. -/
theorem authCost_body {H : List UInt8 → BitVec 256} (ep : Nat) (hep : ep < 2 ^ 32) (L : Nat)
    (hL : L < 32) (s : MachineState) (hI : AuthCostInv ep L s) :
    RunsN H s (authLevelCost ep L) (AuthCostInv ep (L + 1)) := by
  obtain ⟨hcode, hpc, h8, h25, h26⟩ := hI
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  rw [if_pos hL] at hpc
  sym_norm at hcode hpc h8 h25 h26
  subst hpc
  have hC : CodeAt C (addr idxAuth) auth 0 := by rw [hcode]; exact verifierCode_auth
  sym_code hC [auth, authPre, authLoop] [authBody, authSelect, authHash]
  obtain ⟨-, -, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38,
    f39, -, -⟩ := hC
  have hb : (R .x8 >>> ((R .x25).toNat % 64) &&& 1#64 = 0#64) ↔ ep.testBit L = false := by
    rw [h8, h25, cost_shamt L (by omega)]; exact cost_bit_test ep L hep
  have hv26 : isValidDwordAccess (R .x26 + 0#64) = true := by
    rw [h26, BitVec.add_zero]; apply valid_of_range <;>
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] <;> omega
  have hv26' : isValidDwordAccess (R .x26 + 8#64) = true := by
    rw [h26]; apply valid_of_range <;>
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] <;> omega
  by_cases ht : ep.testBit L
  · rw [show authLevelCost ep L = 37 by simp only [authLevelCost, ht, if_true]]
    symc_ld_with f2 hv26; symc_ld_with f3 hv26'
    symc_plain f4; symc_ld f5; symc_ld f6
    symc_plain f7; symc_plain f8; symc_plain f9
    rw [if_neg (fun hh => by simp only [hb.mp hh, Bool.false_eq_true] at ht)]
    symc_sd f10; symc_sd f11; symc_sd f12; symc_sd f13; symc_plain f14
    symc_plain f17; symc_plain f18; symc_plain f19; symc_plain f20; symc_sd f21
    symc_plain f22; symc_plain f23; symc_plain f24; symc_sd f25
    symc_plain f26; symc_plain f27; symc_plain f28; symc_plain f29
    symc_hash f30
    symc_plain f31; symc_ld f32; symc_ld f33; symc_plain f34; symc_sd f35; symc_sd f36
    symc_plain f37; symc_plain f38; symc_plain f39
    exact authCost_tail ep L hL _ ⟨hcode, by sym_norm,
      by sym_norm; exact h8, by sym_norm; rw [h25]; exact cost_ofNat_succ L,
      by sym_norm; rw [h26]; exact cost_ptr_succ _ L, by sym_norm⟩
  · have ht' : ep.testBit L = false := by simpa using ht
    rw [show authLevelCost ep L = 34 by simp only [authLevelCost, ht', Bool.false_eq_true, if_false]]
    symc_ld_with f2 hv26; symc_ld_with f3 hv26'
    symc_plain f4; symc_ld f5; symc_ld f6
    symc_plain f7; symc_plain f8; symc_plain f9
    rw [if_pos (hb.mpr ht')]
    symc_sd f15; symc_sd f16
    symc_plain f17; symc_plain f18; symc_plain f19; symc_plain f20; symc_sd f21
    symc_plain f22; symc_plain f23; symc_plain f24; symc_sd f25
    symc_plain f26; symc_plain f27; symc_plain f28; symc_plain f29
    symc_hash f30
    symc_plain f31; symc_ld f32; symc_ld f33; symc_plain f34; symc_sd f35; symc_sd f36
    symc_plain f37; symc_plain f38; symc_plain f39
    exact authCost_tail ep L hL _ ⟨hcode, by sym_norm,
      by sym_norm; exact h8, by sym_norm; rw [h25]; exact cost_ofNat_succ L,
      by sym_norm; rw [h26]; exact cost_ptr_succ _ L, by sym_norm⟩

/-! ## The region -/

/-- The exact step cost of the authentication-path region. -/
def authSteps (ep : Nat) : Nat := 1090 + 3 * popcount32 ep

theorem authSteps_eq (ep : Nat) : 2 + costSum (authLevelCost ep) 32 = authSteps ep := by
  have h : costSum (authLevelCost ep) 32
      = costSum (fun _ => 34) 32 + costSum (fun i => 3 * (if ep.testBit i then 1 else 0)) 32 := by
    rw [← costSum_add]; rfl
  rw [authSteps, popcount32, h, costSum_const, costSum_mul_left]
  omega

/-- `authPre`: two `LI`s, establishing the invariant at level 0. -/
theorem authCost_entry {H : List UInt8 → BitVec 256} (ep : Nat) (s : MachineState)
    (hcode : s.code = verifierCode) (hpc : s.pc = addr idxAuth)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 ep) : RunsN H s 2 (AuthCostInv ep 0) := by
  obtain ⟨R, M, C, pc, c, pv, pi, ib⟩ := s
  sym_norm at hcode hpc h8
  subst hpc
  have hC : CodeAt C (addr idxAuth) auth 0 := by rw [hcode]; exact verifierCode_auth
  sym_code hC [auth, authPre, authLoop] [authBody, authSelect, authHash]
  obtain ⟨f0, f1, -⟩ := hC
  symc_plain f0; symc_plain f1
  exact RunsN.done ⟨hcode, by sym_norm, by sym_norm; exact h8, by sym_norm, by sym_norm⟩

/-- **The authentication path costs `1090 + 3 * popcount32 ep` steps.**

    The cost is independent of the signature, of the public parameter and of
    every byte in memory: bit `L` of the epoch is the only thing the region's
    control flow ever branches on. -/
theorem authCost_correct {H : List UInt8 → BitVec 256} (ep : Nat) (hep : ep < 2 ^ 32)
    (s : MachineState) (hcode : s.code = verifierCode) (hpc : s.pc = addr idxAuth)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 ep) :
    RunsN H s (authSteps ep) (fun s' => s'.pc = addr idxFinal) := by
  rw [← authSteps_eq]
  refine RunsN.bind (authCost_entry ep s hcode hpc h8) fun s1 h1 => ?_
  refine RunsN.mono (RunsN.loopSum (authLevelCost ep) 32
    (fun L s' hL hI => authCost_body ep hep L hL s' hI) s1 h1) fun s' hI => ?_
  exact hI.2.1.trans (if_neg (by omega))

/-! ## Worst case

`authSteps` is monotone in the population count, so the accepting epoch that
costs the most machine steps is `2 ^ 32 - 1`, and it is the only one. This is
the justification for the `valid-epmax` benchmark fixture. -/

theorem authSteps_le (ep : Nat) : authSteps ep ≤ authSteps (2 ^ 32 - 1) := by
  rw [authSteps, authSteps, popcount32_max]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 (popcount32_le ep)) 1090

theorem authSteps_max : authSteps (2 ^ 32 - 1) = 1186 := by
  rw [authSteps, popcount32_max]

theorem authSteps_lt_of_ne (ep : Nat) (hep : ep < 2 ^ 32) (hne : ep ≠ 2 ^ 32 - 1) :
    authSteps ep < authSteps (2 ^ 32 - 1) := by
  rw [authSteps, authSteps, popcount32_max]
  have := popcount32_lt_of_ne ep hep hne
  omega

end XmssAsm
