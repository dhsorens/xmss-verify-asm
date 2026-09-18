/-
  XmssAsm.Verify

  The end-to-end theorem: the RV64 verifier satisfies `VerifierCorrect H` for
  every hash oracle `H`. Nothing here executes an instruction; the six region
  contracts are composed with `Runs.bind`, and the only facts about the whole
  program are the nine `verifierCode_*` placement facts. LEGACY file.
-/

import XmssAsm.Regions.Init
import XmssAsm.Regions.Decode
import XmssAsm.Regions.Chains
import XmssAsm.Regions.Leaf
import XmssAsm.Regions.Auth
import XmssAsm.Regions.Final
import XmssAsm.Contract

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-! ## Every region writes inside the scratch area -/

theorem WChain_scratch (a : Word) (h : WChain a) : InScratch a := by
  simp only [WChain, InRange, BUFA, CUR, InScratch, SCRATCH_LO, SCRATCH_HI,
    BitVec.reduceToNat] at h ⊢
  rcases h with h | h <;> omega

theorem WInit_scratch (a : Word) (h : WInit a) : InScratch a := by
  simp only [WInit, InRange, BUFA, BUFL_P, OUT, InScratch, SCRATCH_LO, SCRATCH_HI,
    BitVec.reduceToNat] at h ⊢
  rcases h with h | h | h <;> omega

theorem WDecode_scratch (a : Word) (h : WDecode a) : InScratch a := by
  simp only [WDecode, InRange, DIGITS, InScratch, SCRATCH_LO, SCRATCH_HI, BitVec.reduceToNat] at h ⊢
  omega

theorem WChains_scratch (a : Word) (h : WChains a) : InScratch a := by
  rcases h with h | h
  · exact WChain_scratch a h
  · simp only [InRange, ENDPTS, InScratch, SCRATCH_LO, SCRATCH_HI, BitVec.reduceToNat] at h ⊢
    omega

theorem WLeaf_scratch (a : Word) (h : WLeaf a) : InScratch a := by
  simp only [WLeaf, InRange, BUFL, CUR, OUT, InScratch, SCRATCH_LO, SCRATCH_HI,
    BitVec.reduceToNat] at h ⊢
  rcases h with h | h | h <;> omega

theorem WAuth_scratch (a : Word) (h : WAuth a) : InScratch a := by
  simp only [WAuth, InRange, BUFA, CUR, OUT, InScratch, SCRATCH_LO, SCRATCH_HI,
    BitVec.reduceToNat] at h ⊢
  rcases h with h | h | h <;> omega

theorem WNone_scratch (a : Word) (h : (fun _ : Word => False) a) : InScratch a := h.elim

/-! ## The input area is below the scratch area, so every region preserves it -/

theorem not_scratch_of_lt (a : Word) (h : a.toNat < 0x10500) : ¬ InScratch a := by
  simp only [InScratch, SCRATCH_LO, SCRATCH_HI, BitVec.reduceToNat, not_and, Nat.not_lt]
  omega

theorem not_scratch_root : ¬ InScratch ROOT ∧ ¬ InScratch (ROOT + 8) := by
  constructor <;> apply not_scratch_of_lt <;> simp only [ROOT, BitVec.reduceAdd, BitVec.reduceToNat] <;> omega

theorem not_scratch_chains (i : ChainIndex) :
    ¬ InScratch (CHAINS + BitVec.ofNat 64 (16 * i.val)) ∧
    ¬ InScratch (CHAINS + BitVec.ofNat 64 (16 * i.val) + 8) := by
  have hi : i.val < 42 := i.isLt
  constructor <;> apply not_scratch_of_lt <;>
    simp only [CHAINS, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow] <;> omega

theorem not_scratch_auth (l : MerkleLevel) :
    ¬ InScratch (AUTH + BitVec.ofNat 64 (16 * l.val)) ∧
    ¬ InScratch (AUTH + BitVec.ofNat 64 (16 * l.val) + 8) := by
  have hl : l.val < 32 := l.isLt
  constructor <;> apply not_scratch_of_lt <;>
    simp only [AUTH, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow] <;> omega

/-! ## Scratch cells one region keeps for the next -/

theorem not_WDecode_bufaP : ¬ WDecode BUFA_P ∧ ¬ WDecode (BUFA_P + 8) := by
  simp only [WDecode, InRange, DIGITS, BUFA_P]; decide

theorem not_WDecode_buflP : ¬ WDecode BUFL_P ∧ ¬ WDecode (BUFL_P + 8) := by
  simp only [WDecode, InRange, DIGITS, BUFL_P]; decide

theorem not_WChains_buflP : ¬ WChains BUFL_P ∧ ¬ WChains (BUFL_P + 8) := by
  simp only [WChains, WChain, InRange, BUFA, CUR, ENDPTS, BUFL_P, not_or]; decide

theorem not_WLeaf_bufaP : ¬ WLeaf BUFA_P ∧ ¬ WLeaf (BUFA_P + 8) := by
  simp only [WLeaf, InRange, BUFL, CUR, OUT, BUFA_P, not_or]; decide

/-! ## The specification's result, in the shape the machine computes it -/

/-- `Ver(pk, ep, m, σ)` evaluated at `H`, written with the region-level
    abbreviations: the encoding digest, the recovered chain endpoints, the
    leaf, and the root after 32 authentication levels. -/
def specResult (H : HashInput → HashOutput) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) : Bool :=
  match TargetSum.decodeDigest (encD H pk.parameter ep msg sig.randomness) with
  | none => false
  | some enc =>
    decide (authD H pk.parameter ep sig
      (leafD H pk.parameter ep fun i => recoverD H pk.parameter ep i (enc i) (sig.chainValue i)) 32
      = pk.root)

theorem specResult_eq (H : HashInput → HashOutput) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) :
    evalH H (Concrete.verify pk ep msg sig : OracleComp HashSpec Bool) = specResult H pk ep msg sig := by
  rw [evalH_verify]
  rfl

/-! ## The composition -/

theorem verify_runs (H : HashInput → HashOutput) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) (s : MachineState) (hcode : s.code = verifierCode) (hpc : s.pc = CODE_BASE)
    (hrep : Represents s pk ep msg sig) :
    Runs H s (fun s' => Decomp.SyscallHalted s' ∧ stepH H s' = none ∧
      s'.getReg .x10 = resultWord (specResult H pk ep msg sig) ∧ Frame InScratch s s') := by
  have hrepc := hrep
  obtain ⟨hroot, -, -, -, -, hchains, hauth⟩ := hrepc
  -- init
  refine Runs.bind (init_correct H s (by rw [hcode]; exact verifierCode_init) pk ep msg sig hpc hrep) ?_
  intro s1 h1
  obtain ⟨hpc1, h8₁, h20₁, h21₁, hP₁, hPL₁, hfr₁⟩ := h1
  have hcode₁ : s1.code = verifierCode := hfr₁.code.trans hcode
  have hS₁ : Frame InScratch s s1 := hfr₁.mono WInit_scratch
  -- decode
  refine Runs.bind (decode_correct H s1 (by rw [hcode₁]; exact verifierCode_decode)
    (encD H pk.parameter ep msg sig.randomness) hpc1 h20₁ h21₁) ?_
  intro s2 h2
  obtain ⟨hacc, hrej⟩ := h2
  unfold specResult
  cases hdec : TargetSum.decodeDigest (encD H pk.parameter ep msg sig.randomness) with
  | none =>
    obtain ⟨hhalt, hstop, hx10, hfr₂⟩ := hrej hdec
    exact Runs.done ⟨hhalt, hstop, by rw [hx10]; rfl,
      hS₁.trans (hfr₂.mono WDecode_scratch)⟩
  | some enc =>
    obtain ⟨hpc2, h8₂, hdig₂, hfr₂⟩ := hacc enc hdec
    have hcode₂ : s2.code = verifierCode := hfr₂.code.trans hcode₁
    have hS₂ : Frame InScratch s s2 := hS₁.trans (hfr₂.mono WDecode_scratch)
    have hP₂ : HasDigest s2 BUFA_P pk.parameter :=
      ⟨(hfr₂.mem _ not_WDecode_bufaP.1).trans hP₁.1, (hfr₂.mem _ not_WDecode_bufaP.2).trans hP₁.2⟩
    have hPL₂ : HasDigest s2 BUFL_P pk.parameter :=
      ⟨(hfr₂.mem _ not_WDecode_buflP.1).trans hPL₁.1, (hfr₂.mem _ not_WDecode_buflP.2).trans hPL₁.2⟩
    have hchains₂ : ∀ i : ChainIndex,
        HasDigest s2 (CHAINS + BitVec.ofNat 64 (16 * i.val)) (sig.chainValue i) := fun i =>
      ⟨(hS₂.mem _ (not_scratch_chains i).1).trans (hchains i).1,
       (hS₂.mem _ (not_scratch_chains i).2).trans (hchains i).2⟩
    -- chains
    refine Runs.bind (chains_correct H s2 (by rw [hcode₂]; exact verifierCode_chainsPre)
      (by rw [hcode₂]; exact verifierCode_chainLoad) (by rw [hcode₂]; exact verifierCode_chainWalk)
      (by rw [hcode₂]; exact verifierCode_chainsTail) pk.parameter ep enc sig.chainValue
      hpc2 (h8₂.trans h8₁) hP₂ hchains₂ hdig₂) ?_
    intro s3 h3
    obtain ⟨hpc3, h8₃, hend₃, hfr₃⟩ := h3
    have hcode₃ : s3.code = verifierCode := hfr₃.code.trans hcode₂
    have hS₃ : Frame InScratch s s3 := hS₂.trans (hfr₃.mono WChains_scratch)
    have hPL₃ : HasDigest s3 BUFL_P pk.parameter :=
      ⟨(hfr₃.mem _ not_WChains_buflP.1).trans hPL₂.1, (hfr₃.mem _ not_WChains_buflP.2).trans hPL₂.2⟩
    -- leaf
    refine Runs.bind (leaf_correct H s3 (by rw [hcode₃]; exact verifierCode_leaf) pk.parameter ep
      (fun i => recoverD H pk.parameter ep i (enc i) (sig.chainValue i)) hpc3
      h8₃ hPL₃ hend₃) ?_
    intro s4 h4
    obtain ⟨hpc4, h8₄, hcur₄, hfr₄⟩ := h4
    have hcode₄ : s4.code = verifierCode := hfr₄.code.trans hcode₃
    have hS₄ : Frame InScratch s s4 := hS₃.trans (hfr₄.mono WLeaf_scratch)
    have hP₄ : HasDigest s4 BUFA_P pk.parameter :=
      ⟨(hfr₄.mem _ not_WLeaf_bufaP.1).trans ((hfr₃.mem _ (fun h => not_WChains_bufaP.1 h)).trans hP₂.1),
       (hfr₄.mem _ not_WLeaf_bufaP.2).trans ((hfr₃.mem _ (fun h => not_WChains_bufaP.2 h)).trans hP₂.2)⟩
    have hauth₄ : ∀ l : MerkleLevel,
        HasDigest s4 (AUTH + BitVec.ofNat 64 (16 * l.val)) (sig.authPath l) := fun l =>
      ⟨(hS₄.mem _ (not_scratch_auth l).1).trans (hauth l).1,
       (hS₄.mem _ (not_scratch_auth l).2).trans (hauth l).2⟩
    -- auth
    refine Runs.bind (auth_correct H s4 (by rw [hcode₄]; exact verifierCode_auth) pk.parameter ep sig
      (leafD H pk.parameter ep fun i => recoverD H pk.parameter ep i (enc i) (sig.chainValue i))
      hpc4 h8₄ hcur₄ hP₄ hauth₄) ?_
    intro s5 h5
    obtain ⟨hpc5, hcur₅, hfr₅⟩ := h5
    have hcode₅ : s5.code = verifierCode := hfr₅.code.trans hcode₄
    have hS₅ : Frame InScratch s s5 := hS₄.trans (hfr₅.mono WAuth_scratch)
    have hroot₅ : HasDigest s5 ROOT pk.root :=
      ⟨(hS₅.mem _ not_scratch_root.1).trans hroot.1, (hS₅.mem _ not_scratch_root.2).trans hroot.2⟩
    -- final
    refine Runs.mono (final_correct H s5 (by rw [hcode₅]; exact verifierCode_final) _ pk.root hpc5
      hcur₅ hroot₅) ?_
    intro s6 h6
    obtain ⟨hhalt, hstop, hx10, hfr₆⟩ := h6
    exact ⟨hhalt, hstop, hx10, hS₅.trans (hfr₆.mono WNone_scratch)⟩

/-- **The artifact is correct.** For every hash oracle `H`, the 185-instruction
    RV64 program `verifier` loaded at `CODE_BASE`, started at `CODE_BASE` on any
    machine state whose memory represents `(pk, ep, msg, sig)`, halts with `a0`
    equal to the specification's `Ver(pk, ep, msg, sig)` evaluated at `H`, and
    touches nothing outside the scratch area. -/
theorem xmss_verify_correct (H : HashInput → HashOutput) : VerifierCorrect H := by
  intro pk ep msg sig s hcode hpc hrep
  obtain ⟨s', hreach, hhalt, hstop, hx10, hfr⟩ := verify_runs H pk ep msg sig s hcode hpc hrep
  exact ⟨s', hreach, hhalt, hstop, by rw [hx10, specResult_eq], hfr⟩

/-- The theorem applied to the state the differential harness builds. This is
    the exact claim the executable suite checks on every fixture. -/
theorem initState_verify (H : HashInput → HashOutput) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) :
    ∃ s', Reaches H (initState pk ep msg sig) s' ∧ Decomp.SyscallHalted s' ∧ stepH H s' = none ∧
      s'.getReg .x10 = resultWord (evalH H (Concrete.verify pk ep msg sig : OracleComp HashSpec Bool)) ∧
      Frame InScratch (initState pk ep msg sig) s' :=
  xmss_verify_correct H pk ep msg sig (initState pk ep msg sig) (initState_code pk ep msg sig)
    (initState_pc pk ep msg sig) (initState_represents pk ep msg sig)

end XmssAsm
