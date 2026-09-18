/-
  XmssAsm.Machine.Layout

  The fixed machine-memory layout of the verifier: where the structured inputs
  live, where the scratch buffers live, and the word-level encodings of the
  specification's values. Everything is doubleword-aligned and every address
  is a literal in the machine model's legacy zone `[0x20, 0x78000000]`, so
  every access-validity fact below is a `decide`.

  Encodings (all little-endian):

  * a 128-bit digest `d` occupies two doublewords, `d[0:64)` then `d[64:128)`;
  * an epoch `ep < 2^32` occupies one doubleword holding `ep`;
  * the 256-bit message occupies four doublewords, the 192-bit randomness three;
  * `sig.chainValue i` is the digest at `CHAINS + 16 i`, `sig.authPath l` the
    digest at `AUTH + 16 l`.

  The scratch region `[SCRATCH_LO, SCRATCH_HI)` is the only memory the verifier
  writes. Its two hash-input buffers `BUFA` (tweak ‖ P ‖ payload ≤ 64 bytes)
  and `BUFL` (tweak ‖ P ‖ 42 endpoints) are laid out so that a hash input is
  always a contiguous run of doublewords, and the current chain/authentication
  value `CUR` *is* the payload slot of `BUFA`.
-/

module

public import XmssAsm.Upstream

@[expose] public section

namespace XmssAsm

open RiscvZkvm.Rv64

/-! ## Inputs (read-only) -/

def ROOT   : Word := 0x10000  -- pk.root, 16 bytes
def PARAM  : Word := 0x10010  -- pk.parameter, 16 bytes
def EPOCH  : Word := 0x10020  -- epoch, 8 bytes
def MSG    : Word := 0x10028  -- message, 32 bytes
def RHO    : Word := 0x10048  -- sig.randomness, 24 bytes
def CHAINS : Word := 0x10060  -- sig.chainValue, 42 × 16 bytes, ends 0x10300
def AUTH   : Word := 0x10300  -- sig.authPath, 32 × 16 bytes, ends 0x10500

/-! ## Scratch (the only memory the verifier writes) -/

def SCRATCH_LO : Word := 0x10500
def BUFA   : Word := 0x10500  -- hash input A: tweak(16) ‖ P(16) ‖ payload(≤ 64)
def BUFA_P : Word := 0x10510  -- P inside BUFA
def CUR    : Word := 0x10520  -- payload slot of BUFA: current chain / node value, 16 bytes
def CUR2   : Word := 0x10530  -- second payload digest (node hash sibling slot)
def OUT    : Word := 0x10560  -- 32-byte hash output
def DIGITS : Word := 0x10580  -- 42 doublewords of digits, ends 0x10730
def BUFL   : Word := 0x10740  -- hash input L: tweak(16) ‖ P(16) ‖ endpoints(672), ends 0x10A20
def BUFL_P : Word := 0x10750
def ENDPTS : Word := 0x10760  -- endpoint i at ENDPTS + 16 i
def SCRATCH_HI : Word := 0x10A20

/-- The scratch region, as a predicate on byte addresses. -/
def InScratch (a : Word) : Prop := SCRATCH_LO.toNat ≤ a.toNat ∧ a.toNat < SCRATCH_HI.toNat

instance (a : Word) : Decidable (InScratch a) := by unfold InScratch; infer_instance

/-! ## Code -/

def CODE_BASE : Word := 0x1000

/-! ## Word encodings -/

/-- Low and high doublewords of a 128-bit digest. -/
def dLo (d : BitVec 128) : Word := d.extractLsb' 0 64
def dHi (d : BitVec 128) : Word := d.extractLsb' 64 64

/-- Rebuild a digest from its two doublewords. -/
def digestOfWords (lo hi : Word) : BitVec 128 := hi ++ lo

theorem digestOfWords_dLo_dHi (d : BitVec 128) : digestOfWords (dLo d) (dHi d) = d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [digestOfWords, dLo, dHi, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp [h]
  · simp only [h, decide_false, Bool.false_and]
    rw [Nat.add_sub_cancel' (Nat.le_of_not_lt h)]
    simp [show i - 64 < 64 by omega]

theorem dLo_digestOfWords (lo hi : Word) : dLo (digestOfWords lo hi) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [dLo, digestOfWords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi']

theorem dHi_digestOfWords (lo hi : Word) : dHi (digestOfWords lo hi) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [dHi, digestOfWords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi']

/-- Two digests agree iff their doublewords agree. -/
theorem digest_eq_iff (d e : BitVec 128) : d = e ↔ dLo d = dLo e ∧ dHi d = dHi e := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← digestOfWords_dLo_dHi d, ← digestOfWords_dLo_dHi e, h1, h2]

/-- A digest held in memory at `a`: two consecutive doublewords. -/
def HasDigest (s : MachineState) (a : Word) (d : BitVec 128) : Prop :=
  s.getMem a = dLo d ∧ s.getMem (a + 8) = dHi d

/-! ## The doublewords of the 256-bit message and 192-bit randomness -/

def mW (m : BitVec 256) (k : Nat) : Word := m.extractLsb' (64 * k) 64
def rW (r : BitVec 192) (k : Nat) : Word := r.extractLsb' (64 * k) 64

def HasMessage (s : MachineState) (a : Word) (m : BitVec 256) : Prop :=
  s.getMem a = mW m 0 ∧ s.getMem (a + 8) = mW m 1 ∧ s.getMem (a + 16) = mW m 2 ∧
    s.getMem (a + 24) = mW m 3

def HasRandomness (s : MachineState) (a : Word) (r : BitVec 192) : Prop :=
  s.getMem a = rW r 0 ∧ s.getMem (a + 8) = rW r 1 ∧ s.getMem (a + 16) = rW r 2

/-! ## Validity facts about the layout -/

/-- Every doubleword-aligned address in `[0x10000, 0x10A20)` is a valid
    doubleword access. -/
theorem valid_of_range (a : Word) (h8 : a.toNat % 8 = 0)
    (hlo : 0x10000 ≤ a.toNat) (hhi : a.toNat < 0x10A20) :
    isValidDwordAccess a = true := by
  simp only [isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START, MEM_END, INPUT_MEM_START,
    INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  omega

end XmssAsm

namespace XmssAsm

open RiscvZkvm.Rv64

/-! ## Frames -/

/-- The byte addresses `[lo, lo + n)`. -/
def InRange (lo : Word) (n : Nat) (a : Word) : Prop :=
  lo.toNat ≤ a.toNat ∧ a.toNat < lo.toNat + n

/-- So that a region's write set can be *evaluated*, and the executable frame
    check in `XmssAsmTests.Regions` can be derived from the very predicate the
    region theorem uses rather than mirrored by hand. A hand-written mirror
    drifts silently the first time a candidate changes a write set. -/
instance InRange.decidable (lo : Word) (n : Nat) (a : Word) : Decidable (InRange lo n a) := by
  unfold InRange; infer_instance

/-- Every register the verifier may write. Everything else is preserved. -/
def CLOB : List Reg :=
  [.x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
   .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .x29, .x30, .x31]

/-- What a region leaves alone: code, the host-I/O fields, every memory cell
    outside its write set `W`, and every register outside `CLOB`. -/
def Frame (W : Word → Prop) (s s' : MachineState) : Prop :=
  s'.code = s.code ∧ s'.committed = s.committed ∧ s'.publicValues = s.publicValues ∧
  s'.privateInput = s.privateInput ∧ s'.inputBufBase = s.inputBufBase ∧
  (∀ a, ¬ W a → s'.getMem a = s.getMem a) ∧ (∀ r, r ∉ CLOB → s'.getReg r = s.getReg r)

theorem Frame.refl (W : Word → Prop) (s : MachineState) : Frame W s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.trans {W : Word → Prop} {s s1 s2 : MachineState}
    (h1 : Frame W s s1) (h2 : Frame W s1 s2) : Frame W s s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   fun a ha => (h2.2.2.2.2.2.1 a ha).trans (h1.2.2.2.2.2.1 a ha),
   fun r hr => (h2.2.2.2.2.2.2 r hr).trans (h1.2.2.2.2.2.2 r hr)⟩

theorem Frame.mono {W W' : Word → Prop} {s s' : MachineState}
    (hW : ∀ a, W a → W' a) (h : Frame W s s') : Frame W' s s' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
   fun a ha => h.2.2.2.2.2.1 a (fun hw => ha (hW a hw)), h.2.2.2.2.2.2⟩

theorem Frame.mem {W : Word → Prop} {s s' : MachineState} (h : Frame W s s') (a : Word)
    (ha : ¬ W a) : s'.getMem a = s.getMem a := h.2.2.2.2.2.1 a ha

theorem Frame.reg {W : Word → Prop} {s s' : MachineState} (h : Frame W s s') (r : Reg)
    (hr : r ∉ CLOB) : s'.getReg r = s.getReg r := h.2.2.2.2.2.2 r hr

theorem Frame.code {W : Word → Prop} {s s' : MachineState} (h : Frame W s s') :
    s'.code = s.code := h.1

/-- The whole scratch region as a write set. -/
theorem InScratch_iff (a : Word) : InScratch a ↔ InRange SCRATCH_LO 0x520 a := by
  simp [InScratch, InRange, SCRATCH_LO, SCRATCH_HI]

end XmssAsm
