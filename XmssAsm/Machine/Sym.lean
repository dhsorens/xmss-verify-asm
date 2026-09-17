/-
  XmssAsm.Machine.Sym

  Symbolic execution of straight-line RV64 code over the hash-oracle stepper.

  A region proof keeps the machine state as a flat record literal
  `{ regs := R, mem := M, code := C, pc := lit, ... }`. One `sym_*` step

    1. resolves the fetched instruction by kernel evaluation of the code map
       at the literal pc (`sym_fetch`: `dsimp` to expose `C pc`, then `rfl`),
    2. applies the matching `stepH_*` lemma through `Runs.step`, and
    3. renormalises the successor into a record literal (`sym_norm`), so that
       register and memory reads are `if`-chains that the same simp set
       decides for literal registers and literal addresses.

  The simp set is `simp only` with an explicit list of lemmas and simprocs, so
  proof-check time does not depend on the ambient simp set (PLAN R10). Every
  lemma below is either a definitional unfolding of the machine model or a
  literal-arithmetic simproc.
-/

module

public import XmssAsm.Machine.Hash
public import XmssAsm.Machine.Layout
public import XmssAsm.Program.Verifier

@[expose] public section

namespace XmssAsm

open RiscvZkvm.Rv64

theorem regBeq (a b : Reg) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem wordBeq (a b : Word) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem if_if_same {α : Type} (c : Prop) [Decidable c] (a b d : α) :
    (if c then a else if c then b else d) = if c then a else d := by
  by_cases h : c <;> simp [h]

/-- Reading a register other than `x0` is the raw register file. -/
theorem getReg_mk_ne_x0 (R : Reg → Word) (M : Word → Word) (C : CodeMem) (pc : Word)
    (c : List (Word × Word)) (pv pi : List (BitVec 8)) (ib : Word) (r : Reg) (h : r ≠ .x0) :
    MachineState.getReg ⟨R, M, C, pc, c, pv, pi, ib⟩ r = R r := by
  cases r <;> first | exact absurd rfl h | rfl

theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl

/-- The `hashEffect` of a call, exposed as four stores at literal offsets. -/
theorem hashEffect_eq (H : List UInt8 → BitVec 256) (s : MachineState) :
    hashEffect H s =
      ((((s.setMem (s.getReg .x12) ((H (hashInputOf s)).extractLsb' 0 64)).setMem
        (s.getReg .x12 + 8) ((H (hashInputOf s)).extractLsb' 64 64)).setMem
        (s.getReg .x12 + 8 + 8) ((H (hashInputOf s)).extractLsb' 128 64)).setMem
        (s.getReg .x12 + 8 + 8 + 8) ((H (hashInputOf s)).extractLsb' 192 64)).setPC (s.pc + 4) := by
  rfl

end XmssAsm

/-! ## The tactics -/

/-- Normalise a machine state term (and any projections of it) into a flat
    record literal with decided register/memory reads and literal arithmetic. -/
macro "sym_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [RiscvZkvm.Rv64.execInstrBr, RiscvZkvm.Rv64.MachineState.setReg,
      RiscvZkvm.Rv64.MachineState.setPC, RiscvZkvm.Rv64.MachineState.setMem,
      RiscvZkvm.Rv64.MachineState.getReg, RiscvZkvm.Rv64.MachineState.getMem,
      RiscvZkvm.Rv64.signExtend12, RiscvZkvm.Rv64.signExtend13, RiscvZkvm.Rv64.signExtend21,
      XmssAsm.regBeq, XmssAsm.wordBeq, XmssAsm.if_if_same, XmssAsm.hashEffect_eq,
      XmssAsm.hashEffectWith,
      XmssAsm.HASH_ID, XmssAsm.CODE_BASE,
      XmssAsm.ROOT, XmssAsm.PARAM, XmssAsm.EPOCH, XmssAsm.MSG, XmssAsm.RHO, XmssAsm.CHAINS, XmssAsm.AUTH,
      XmssAsm.BUFA, XmssAsm.BUFA_P, XmssAsm.CUR, XmssAsm.CUR2, XmssAsm.OUT, XmssAsm.DIGITS,
      XmssAsm.BUFL, XmssAsm.BUFL_P, XmssAsm.ENDPTS, XmssAsm.addr,
      XmssAsm.idxInitPayload_eq, XmssAsm.idxInitHash_eq, XmssAsm.idxDecode_eq, XmssAsm.idxDecodeLoop_eq,
      XmssAsm.idxDecodePost_eq, XmssAsm.idxDecodeReject_eq, XmssAsm.idxChains_eq, XmssAsm.idxChainsLoop_eq,
      XmssAsm.idxChainWalk_eq, XmssAsm.idxChainStore_eq, XmssAsm.idxLeaf_eq, XmssAsm.idxAuth_eq,
      XmssAsm.idxAuthLoop_eq, XmssAsm.idxAuthHash_eq, XmssAsm.idxFinal_eq, XmssAsm.idxAccept_eq,
      XmssAsm.idxReject_eq, XmssAsm.idxEnd_eq, XmssAsm.chainWalk_length,
      XmssAsm.chainWalkA_length, XmssAsm.chainWalkB_length,
      XmssAsm.bOff_decodeLoop, XmssAsm.bOff_chainWalkA, XmssAsm.jOff_chainWalkA, XmssAsm.bOff_chainWalkB,
      XmssAsm.jOff_chainWalkB, XmssAsm.bOff_chainsLoop, XmssAsm.bOff_authLoop,
      XmssAsm.jOff, XmssAsm.bOff, XmssAsm.imm, Int.reduceNeg,
      BitVec.add_zero,
      decide_eq_true_eq, decide_true, decide_false, eq_self_iff_true, reduceCtorEq,
      ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq, not_true_eq_false,
      not_false_eq_true,
      BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceAnd, BitVec.reduceOr,
      BitVec.reduceXOr, BitVec.reduceShiftLeft, BitVec.reduceUShiftRight, BitVec.reduceSignExtend,
      BitVec.reduceZeroExtend, BitVec.reduceSetWidth, BitVec.reduceToNat, BitVec.reduceOfNat,
      BitVec.reduceOfInt, BitVec.isValue, BitVec.reduceEq, BitVec.reduceNe, BitVec.reduceBEq,
      BitVec.reduceExtractLsb', BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
      BitVec.reduceHShiftLeft', BitVec.reduceHShiftRight', BitVec.reduceSLT, BitVec.reduceULT,
      Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow,
      Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT] $[$loc]?)

/-- Resolve `s.code s.pc = some ?i` on a record-literal state by evaluation. -/
macro "sym_fetch" : tactic => `(tactic| (dsimp only; rfl))

/-- Discharge `isValidDwordAccess a = true` for a literal address. -/
macro "sym_valid" : tactic => `(tactic| (sym_norm; decide))

/-- Execute one non-memory, non-syscall instruction. -/
macro "sym_plain" : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_plain (by sym_fetch) (by decide) (by decide) (by decide)) ?_; sym_norm))

/-- Execute one `LD` at a valid literal address. -/
macro "sym_ld" : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_ld (by sym_fetch) (by sym_valid)) ?_; sym_norm))

/-- Execute one `SD` at a valid literal address. -/
macro "sym_sd" : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_sd (by sym_fetch) (by sym_valid)) ?_; sym_norm))

/-- Execute one `LD`/`SD` whose address validity is supplied. -/
macro "sym_ld_with" h:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_ld (by sym_fetch) $h) ?_; sym_norm))
macro "sym_sd_with" h:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_sd (by sym_fetch) $h) ?_; sym_norm))

/-- Execute the hash call; the argument-validity proof is supplied. -/
macro "sym_hash" h:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_hash (by sym_fetch) (by sym_norm; rfl) $h) ?_; sym_norm))

/-- Turn `hC : CodeAt C base prog k` into one literal fetch fact per instruction.
    The `outer` definitions are unfolded first (so loop branch offsets that
    mention an inner block's length are evaluated by the offset lemmas before
    that block is unfolded), then the `inner` ones. -/
macro "sym_code" hC:ident "[" outer:Lean.Parser.Tactic.simpLemma,* "]" "[" inner:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [XmssAsm.CodeAt, $outer,*, List.cons_append, List.nil_append] at $hC:ident;
             sym_norm at $hC:ident;
             simp only [XmssAsm.CodeAt, $inner,*, List.cons_append, List.nil_append] at $hC:ident;
             sym_norm at $hC:ident))

/-- `sym_code` for a straight-line region: one unfolding phase. -/
macro "sym_code1" hC:ident "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [XmssAsm.CodeAt, $defs,*, List.cons_append, List.nil_append] at $hC:ident;
             sym_norm at $hC:ident))

/-! ### Steps with an explicit fetch fact `hf : C pc = some i` (abstract code maps) -/

macro "sym_plain_f" hf:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_plain $hf (by decide) (by decide) (by decide)) ?_; sym_norm))
macro "sym_ld_f" hf:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_ld $hf (by sym_valid)) ?_; sym_norm))
macro "sym_sd_f" hf:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_sd $hf (by sym_valid)) ?_; sym_norm))
macro "sym_ld_f_with" hf:ident h:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_ld $hf $h) ?_; sym_norm))
macro "sym_sd_f_with" hf:ident h:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_sd $hf $h) ?_; sym_norm))
macro "sym_hash_in_f" hf:ident inp:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_hash_input (inp := $inp) $hf (by sym_norm <;> rfl) (by simp only [XmssAsm.hashArgsValid, XmssAsm.outBlockValid]; sym_norm <;> decide) ?hin) ?_; rotate_left; sym_norm))

/-- Execute the hash call with a named input `inp`; leaves the goal
    `hashInputOf s = inp` (tagged `hin`) for the state at the call. -/
macro "sym_hash_in" inp:term : tactic =>
  `(tactic| (refine XmssAsm.Runs.step (XmssAsm.stepH_hash_input (inp := $inp) (by sym_fetch)
      (by sym_norm <;> rfl)
      (by simp only [XmssAsm.hashArgsValid, XmssAsm.outBlockValid]; sym_norm <;> decide) ?hin) ?_; rotate_left; sym_norm))

/-- Resolve a branch after `sym_plain` produced `Runs (if c then _ else _) Q`. -/
macro "sym_branch" h:term : tactic =>
  `(tactic| (first | rw [if_pos $h] | rw [if_neg $h] | simp only [$h:term, ite_true, ite_false]))

/-! ## Frame goals -/

/-- Close `∀ a, ¬ W a → s'.getMem a = s.getMem a` for a record-literal `s'`
    whose stores are at literal addresses inside `W`. -/
macro "sym_frame_mem" : tactic =>
  `(tactic| (intro a ha; simp only [XmssAsm.InRange, not_or] at ha; sym_norm at ha ⊢;
             simp (disch := bv_omega) only [if_neg]))

/-- Close `∀ r, r ∉ CLOB → s'.getReg r = s.getReg r` for a record-literal `s'`
    whose register writes are all in `CLOB`. -/
macro "sym_frame_reg" : tactic =>
  `(tactic| (intro r hr;
             simp only [XmssAsm.CLOB, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr;
             sym_norm; simp only [hr, if_false, ite_false, ↓reduceIte]))

/-- `sym_frame_mem` for a named write-set predicate `W` (unfolded first). -/
macro "sym_frame_mem_W" W:ident : tactic =>
  `(tactic| (intro a ha; simp only [$W:ident, XmssAsm.InRange, not_or] at ha; sym_norm at ha;
             sym_norm <;> simp (disch := bv_omega) only [if_neg]))

/-- `Frame W s s'` for a record-literal `s'` and a named write set `W`. -/
macro "sym_frame_W" W:ident : tactic =>
  `(tactic| (refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩; (sym_frame_mem_W $W); (sym_frame_reg)))

/-- The whole `Frame W s s'` obligation for a record-literal `s'`. -/
macro "sym_frame" : tactic =>
  `(tactic| (refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩; (sym_frame_mem); (sym_frame_reg)))
