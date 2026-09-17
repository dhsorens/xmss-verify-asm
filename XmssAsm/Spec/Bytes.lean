/-
  XmssAsm.Spec.Bytes

  The byte-level bridge between the machine and the specification.

  The spec builds hash inputs as `List UInt8` with `bytesLE`; the machine
  holds doublewords and the hash call reads them with the model's `readBytes`.
  Everything here is an identity between the two views:

  * `readBytes_words`: `8 n` bytes read from an aligned address are the
    little-endian bytes of the `n` doublewords there;
  * `bytesLE_add` and its instances: the spec's `bytesLE` of a digest,
    message or randomness is the concatenation of its doublewords' bytes;
  * `fieldBytes_eq`: the 16-byte tweak is two doublewords,
    `tag·2^8 + position·2^32` and `epoch·2^32`;
  * the payload identities `encodingPayload_eq`, `nodePayload_eq`,
    `leafPayload_eq`, and `tweakableHashInput_eq`.

  Legacy file: it imports `XmssSecurity.Scheme`.
-/

import XmssAsm.Machine.Hash
import XmssAsm.Machine.Layout
import XmssSecurity.Scheme
import Mathlib.Tactic.FinCases

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- Little-endian bytes of a list of doublewords. -/
def wordsBytes (ws : List Word) : HashInput := ws.flatMap (fun w => bytesLE 8 w)

@[simp] theorem wordsBytes_nil : wordsBytes [] = [] := rfl

@[simp] theorem wordsBytes_cons (w : Word) (ws : List Word) :
    wordsBytes (w :: ws) = bytesLE 8 w ++ wordsBytes ws := by
  simp [wordsBytes]

@[simp] theorem wordsBytes_append (a b : List Word) :
    wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b := by
  simp [wordsBytes]

/-! ## Bit-level facts about `bytesLE` -/

theorem UInt8.ofBitVec_inj_iff (a b : BitVec 8) : UInt8.ofBitVec a = UInt8.ofBitVec b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩

theorem extractLsb'_extractLsb' {w : Nat} (v : BitVec w) (s l a b : Nat) (h : a + b ≤ l) :
    (v.extractLsb' s l).extractLsb' a b = v.extractLsb' (s + a) b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  have : a + j < l := by omega
  simp [hj, this, Nat.add_assoc]

theorem wordsBytes_length (ws : List Word) : (wordsBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [wordsBytes_cons, ih, bytesLE]; omega

/-- Byte `k` of a word list is byte `k % 8` of word `k / 8`. -/
theorem wordsBytes_getElem? (ws : List Word) (k : Nat) :
    (wordsBytes ws)[k]? = (ws[k / 8]?).map (fun w => UInt8.ofBitVec (w.extractLsb' (8 * (k % 8)) 8)) := by
  induction ws generalizing k with
  | nil => simp
  | cons w ws ih =>
    rw [wordsBytes_cons, List.getElem?_append]
    by_cases h : k < 8
    · have h0 : k / 8 = 0 := by omega
      simp only [bytesLE, List.length_ofFn, h, ↓reduceIte, List.getElem?_ofFn, ↓reduceDIte, h0,
        List.getElem?_cons_zero, Option.map_some, Nat.mod_eq_of_lt h]
    · have h1 : k / 8 = (k - 8) / 8 + 1 := by omega
      have h2 : (k - 8) % 8 = k % 8 := by omega
      simp only [bytesLE, List.length_ofFn, h, ↓reduceIte, ih, h1, List.getElem?_cons_succ, h2]

/-- A serialisation of `8 n` bytes is the bytes of its `n` doublewords. -/
theorem bytesLE_eq_wordsBytes (N n : Nat) (hN : N = 8 * n) (v : BitVec (8 * N)) :
    bytesLE N v = wordsBytes (List.ofFn fun j : Fin n => v.extractLsb' (64 * j.val) 64) := by
  apply List.ext_getElem?
  intro k
  rw [wordsBytes_getElem?]
  simp only [bytesLE, List.getElem?_ofFn]
  by_cases hk : k < N
  · have hq : k / 8 < n := by omega
    simp only [hk, ↓reduceDIte, hq, Option.map_some, Option.some.injEq]
    rw [UInt8.ofBitVec_inj_iff, extractLsb'_extractLsb' _ _ _ _ _ (by omega)]
    congr 1; omega
  · have hq : ¬ k / 8 < n := by omega
    simp [hk, hq]

theorem bytesLE_digest (d : Digest) : bytesLE 16 d = wordsBytes [dLo d, dHi d] := by
  rw [bytesLE_eq_wordsBytes 16 2 rfl d]
  simp [List.ofFn_succ, dLo, dHi]

theorem bytesLE_param (P : PublicParameter) : bytesLE 16 P = wordsBytes [dLo P, dHi P] := by
  rw [bytesLE_eq_wordsBytes 16 2 rfl P]
  simp [List.ofFn_succ, dLo, dHi]

theorem bytesLE_message (m : Message) : bytesLE 32 m = wordsBytes [mW m 0, mW m 1, mW m 2, mW m 3] := by
  rw [bytesLE_eq_wordsBytes 32 4 rfl m]
  simp [List.ofFn_succ, mW]

theorem bytesLE_randomness (r : Randomness) : bytesLE 24 r = wordsBytes [rW r 0, rW r 1, rW r 2] := by
  rw [bytesLE_eq_wordsBytes 24 3 rfl r]
  simp [List.ofFn_succ, rW]

theorem bytesLE_zero : bytesLE 8 (0 : Word) = List.replicate 8 0 := rfl

/-! ## Tweaks as two doublewords -/

/-- The first tweak doubleword: `0 ‖ tag ‖ 0 ‖ 0 ‖ position`. -/
def tw0 (tag pos : Nat) : Word := BitVec.ofNat 64 (tag * 2 ^ 8 + pos * 2 ^ 32)

/-- The second tweak doubleword: `0^4 ‖ epoch`. -/
def tw1 (e : Nat) : Word := BitVec.ofNat 64 (e * 2 ^ 32)

theorem UInt8.ofBitVec_eq_iff (a b : BitVec 8) :
    UInt8.ofBitVec a = UInt8.ofBitVec b ↔ a.toNat = b.toNat := by
  rw [UInt8.ofBitVec_inj_iff, BitVec.toNat_eq]

theorem UInt8.zero_eq_ofBitVec_iff (b : BitVec 8) : (0 : UInt8) = UInt8.ofBitVec b ↔ b.toNat = 0 := by
  constructor
  · intro h; have := congrArg UInt8.toBitVec h; simp at this; rw [← this]; rfl
  · intro h; apply UInt8.eq_of_toBitVec_eq; simp; exact (BitVec.toNat_eq.mpr (by simpa using h)).symm

theorem fieldBytes_eq (tag pos e : Nat) (htag : tag < 2 ^ 8) (hpos : pos < 2 ^ 32) (he : e < 2 ^ 32) :
    fieldBytes (tweakFields tag pos e) = bytesLE 8 (tw0 tag pos) ++ bytesLE 8 (tw1 e) := by
  simp only [fieldBytes, tweakFields, protocolDomainSep, bytesLE, List.ofFn_succ,
    List.ofFn_zero, List.replicate, List.cons_append, List.nil_append, List.cons.injEq, and_true,
    Fin.val_zero, Fin.val_succ, Nat.mul_zero, Nat.zero_add, UInt8.ofBitVec_eq_iff,
    UInt8.zero_eq_ofBitVec_iff, tw0, tw1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    repeat rw [BitVec.extractLsb'_toNat]
    repeat rw [BitVec.toNat_ofNat]
    repeat rw [Nat.shiftRight_eq_div_pow]
    omega

theorem tweakBytes_chain (ep : Epoch) (i : ChainIndex) (step : ChainStep) :
    tweakBytes (.chain ep i step) = wordsBytes [tw0 1 (8 * i.val + step.val), tw1 ep.val] := by
  have hi := i.isLt; have hs := step.isLt; have he := ep.isLt
  simp only [numChains, chainLength, winternitzBits, lifetime, treeHeight] at hi hs he
  simp only [tweakBytes, hashDomainFields, chainLength, winternitzBits, wordsBytes, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Nat.reducePow]
  rw [fieldBytes_eq 1 (8 * i.val + step.val) ep.val (by decide) (by omega) (by omega)]

theorem tweakBytes_leaf (ep : Epoch) :
    tweakBytes (.leaf ep) = wordsBytes [tw0 2 0, tw1 ep.val] := by
  have he := ep.isLt
  simp only [lifetime, treeHeight] at he
  simp only [tweakBytes, hashDomainFields, wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [fieldBytes_eq 2 0 ep.val (by decide) (by decide) (by omega)]

theorem tweakBytes_encoding (ep : Epoch) :
    tweakBytes (.encoding ep) = wordsBytes [tw0 4 0, tw1 ep.val] := by
  have he := ep.isLt
  simp only [lifetime, treeHeight] at he
  simp only [tweakBytes, hashDomainFields, wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [fieldBytes_eq 4 0 ep.val (by decide) (by decide) (by omega)]

theorem tweakBytes_merkle (level : MerkleLevel) (node : MerkleNode) :
    tweakBytes (.merkle level node) = wordsBytes [tw0 3 (level.val + 1), tw1 node.val] := by
  have hl := level.isLt; have hn := node.isLt
  simp only [treeHeight, lifetime] at hl hn
  simp only [tweakBytes, hashDomainFields, wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [fieldBytes_eq 3 (level.val + 1) node.val (by decide) (by omega) (by omega)]

/-! ## Payloads -/

theorem tweakableHashInput_eq (P : PublicParameter) (dom : HashDomain) (payload : HashInput)
    (ws : List Word) (h : tweakBytes dom = wordsBytes ws) :
    tweakableHashInput P dom payload = wordsBytes (ws ++ [dLo P, dHi P]) ++ payload := by
  simp only [tweakableHashInput, h, bytesLE_param, wordsBytes_append, List.append_assoc]

theorem encodingPayload_eq (msg : Message) (rho : Randomness) :
    Concrete.encodingPayload msg rho =
      wordsBytes [mW msg 0, mW msg 1, mW msg 2, mW msg 3, rW rho 0, rW rho 1, rW rho 2, 0] := by
  simp only [Concrete.encodingPayload, bytesLE_message, bytesLE_randomness, ← bytesLE_zero]
  simp [wordsBytes]

theorem nodePayload_eq (l r : Digest) :
    Concrete.nodePayload l r = wordsBytes [dLo l, dHi l, dLo r, dHi r] := by
  simp only [Concrete.nodePayload, bytesLE_digest]
  simp [wordsBytes]

/-- The doublewords of a list of digests, in memory order. -/
def digestsWords (ds : List Digest) : List Word := ds.flatMap (fun d => [dLo d, dHi d])

@[simp] theorem digestsWords_nil : digestsWords [] = [] := rfl
@[simp] theorem digestsWords_cons (d : Digest) (ds : List Digest) :
    digestsWords (d :: ds) = dLo d :: dHi d :: digestsWords ds := rfl

theorem leafPayload_eq (e : ChainIndex → Digest) :
    Concrete.leafPayload e = wordsBytes (digestsWords (List.ofFn e)) := by
  show (List.ofFn e).flatMap (fun d : Digest => bytesLE 16 d) = _
  generalize List.ofFn e = ds
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.flatMap_cons, bytesLE_digest, ih]; simp [wordsBytes]

/-! ## Truncation -/

theorem dLo_truncateHash (o : HashOutput) : dLo (truncateHash o) = o.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [dLo, truncateHash, digestBits, hj]

theorem dHi_truncateHash (o : HashOutput) : dHi (truncateHash o) = o.extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [dHi, truncateHash, digestBits, hj]

/-! ## Reading doublewords back as bytes -/

theorem readBytes_add (s : MachineState) (a : Word) (m n : Nat) :
    s.readBytes a (m + n) = s.readBytes a m ++ s.readBytes (a + BitVec.ofNat 64 m) n := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, MachineState.readBytes_succ, MachineState.readBytes_succ, ih]
    simp only [List.cons_append, List.cons.injEq, true_and]
    congr 2
    bv_omega

/-- `extractByte` is `extractLsb'`. -/
theorem extractByte_eq (w : Word) (k : Nat) : extractByte w k = w.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat]
  rw [Nat.mul_comm]

theorem readBytes_getElem? (s : MachineState) :
    ∀ (n : Nat) (a : Word) (k : Nat),
      (s.readBytes a n)[k]? = if k < n then some (s.getByte (a + BitVec.ofNat 64 k)) else none := by
  intro n
  induction n with
  | zero => intro a k; simp
  | succ n ih =>
    intro a k
    rw [MachineState.readBytes_succ]
    cases k with
    | zero => simp
    | succ k =>
      rw [List.getElem?_cons_succ, ih]
      have : a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by bv_omega
      simp only [this, Nat.add_lt_add_iff_right]

theorem readBytes_dword (s : MachineState) (a : Word) (h8 : a.toNat % 8 = 0)
    (hlt : a.toNat + 8 < 2 ^ 64) :
    (s.readBytes a 8).map UInt8.ofBitVec = bytesLE 8 (s.getMem a) := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, readBytes_getElem?]
  simp only [bytesLE, List.getElem?_ofFn]
  by_cases hk : k < 8
  · simp only [hk, ↓reduceIte, ↓reduceDIte, Option.map_some, Option.some.injEq]
    rw [UInt8.ofBitVec_inj_iff]
    simp only [MachineState.getByte]
    have h1 : alignToDword (a + BitVec.ofNat 64 k) = a := by
      rw [alignToDword_add_ofNat_of_aligned h8 (by omega), Nat.div_eq_of_lt hk]; simp
    have h2 : byteOffset (a + BitVec.ofNat 64 k) = k := by
      rw [byteOffset_add_ofNat_of_aligned h8 (by omega), Nat.mod_eq_of_lt hk]
    rw [h1, h2, extractByte_eq]
  · simp [hk]

theorem readBytes_words (s : MachineState) (a : Word) (n : Nat) (h8 : a.toNat % 8 = 0)
    (hlt : a.toNat + 8 * n < 2 ^ 64) :
    (s.readBytes a (8 * n)).map UInt8.ofBitVec = wordsBytes (s.readWords a n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, readBytes_add, List.map_append,
      readBytes_dword s a h8 (by omega), MachineState.readWords_succ, wordsBytes_cons]
    congr 1
    have : a + BitVec.ofNat 64 8 = a + 8 := by simp
    rw [this]
    apply ih
    · bv_omega
    · bv_omega

/-- The hash call's input, when `a1 = 8 n` and `a0` is aligned and in range. -/
theorem hashInputOf_eq (s : MachineState) (n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 (8 * n)) (h8 : (s.getReg .x10).toNat % 8 = 0)
    (hlt : (s.getReg .x10).toNat + 8 * n < 2 ^ 64) :
    hashInputOf s = wordsBytes (s.readWords (s.getReg .x10) n) := by
  unfold hashInputOf
  rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact readBytes_words s _ n h8 hlt

theorem readWords_add (s : MachineState) (a : Word) (m n : Nat) :
    s.readWords a (m + n) = s.readWords a m ++ s.readWords (a + BitVec.ofNat 64 (8 * m)) n := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, MachineState.readWords_succ, MachineState.readWords_succ, ih]
    simp only [List.cons_append, List.cons.injEq, true_and]
    congr 2
    bv_omega

/-- Consecutive digest slots read back as their doublewords. -/
theorem readWords_digests (s : MachineState) : ∀ (n : Nat) (a : Word) (e : Fin n → Digest),
    (∀ i : Fin n, HasDigest s (a + BitVec.ofNat 64 (16 * i.val)) (e i)) →
    s.readWords a (2 * n) = digestsWords (List.ofFn e) := by
  intro n
  induction n with
  | zero => intro a e _; simp
  | succ n ih =>
    intro a e h
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, readWords_add, MachineState.readWords_succ,
      MachineState.readWords_succ, MachineState.readWords_zero, List.ofFn_succ, digestsWords_cons]
    have h0 : s.getMem a = dLo (e 0) ∧ s.getMem (a + 8) = dHi (e 0) := by
      have := h 0; simpa [HasDigest] using this
    rw [h0.1, h0.2]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
    apply ih
    intro i
    have hi := h i.succ
    have : a + BitVec.ofNat 64 (8 * 2) + BitVec.ofNat 64 (16 * i.val) =
        a + BitVec.ofNat 64 (16 * i.succ.val) := by
      simp only [Fin.val_succ]; bv_omega
    rw [this]; exact hi

end XmssAsm
