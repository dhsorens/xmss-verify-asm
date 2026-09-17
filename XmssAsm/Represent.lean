/-
  XmssAsm.Represent

  The machine/specification representation relation, and the one function
  that builds a machine state from structured inputs.

  `Represents s pk ep msg sig` says the input region of `s`'s memory holds the
  encodings of the four structured values, per the layout in
  `XmssAsm.Machine.Layout`. It says nothing about scratch memory, registers,
  or the host-I/O fields: the theorem must hold for all of them.

  `initState` is what the differential tests use to build a machine from a
  fixture; `initState_represents` is the check that the test harness and the
  theorem agree on the representation (PLAN E2).

  Legacy file: it names `XmssSecurity.PublicKey` and friends.
-/

import XmssAsm.Machine.Layout
import XmssAsm.Machine.Eval
import XmssSecurity.Scheme

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity

/-- Memory holds the encoded inputs. -/
def Represents (s : MachineState) (pk : PublicKey) (ep : Epoch) (msg : Message)
    (sig : Signature) : Prop :=
  HasDigest s ROOT pk.root ∧
  HasDigest s PARAM pk.parameter ∧
  s.getMem EPOCH = BitVec.ofNat 64 ep.val ∧
  HasMessage s MSG msg ∧
  HasRandomness s RHO sig.randomness ∧
  (∀ i : ChainIndex, HasDigest s (CHAINS + BitVec.ofNat 64 (16 * i.val)) (sig.chainValue i)) ∧
  (∀ l : MerkleLevel, HasDigest s (AUTH + BitVec.ofNat 64 (16 * l.val)) (sig.authPath l))

/-- The two doublewords of a digest, in memory order. -/
def digestWords (d : Digest) : List Word := [dLo d, dHi d]

/-- The machine state for structured inputs: the blank verifier machine with
    the inputs written at their layout addresses. -/
def initState (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature) : MachineState :=
  (((((((blankState.writeWords ROOT (digestWords pk.root)).writeWords PARAM
    (digestWords pk.parameter)).writeWords EPOCH [BitVec.ofNat 64 ep.val]).writeWords MSG
    [mW msg 0, mW msg 1, mW msg 2, mW msg 3]).writeWords RHO
    [rW sig.randomness 0, rW sig.randomness 1, rW sig.randomness 2]).writeWords CHAINS
    ((List.ofFn sig.chainValue).flatMap digestWords)).writeWords AUTH
    ((List.ofFn sig.authPath).flatMap digestWords))

/-! ## `initState` satisfies `Represents`

PLAN E2 asks the differential harness to build its machine state through the
same representation the theorem assumes. It builds `initState`; the theorem
assumes `Represents`. These lemmas are the bridge, so the harness cannot drift
from the precondition of `xmss_verify_correct`. -/

/-- Addresses inside a doubleword block that does not wrap. -/
theorem block_ne (a base : Word) (n : Nat) (hbase : base.toNat + 8 * n < 2 ^ 64)
    (hout : a.toNat < base.toNat ∨ base.toNat + 8 * n ≤ a.toNat) :
    ∀ k, k < n → a ≠ base + BitVec.ofNat 64 (8 * k) := by
  intro k hk h
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at h'
  omega

theorem addr_succ (base : Word) (k : Nat) :
    base + BitVec.ofNat 64 (8 * (k + 1)) = base + 8 + BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]
  omega

/-- A write outside the block leaves the cell alone. -/
theorem getMem_writeWords_miss (a : Word) : ∀ (ws : List Word) (s : MachineState) (base : Word),
    (∀ k, k < ws.length → a ≠ base + BitVec.ofNat 64 (8 * k)) →
    (s.writeWords base ws).getMem a = s.getMem a := by
  intro ws
  induction ws with
  | nil => intro s base _; rfl
  | cons w ws ih =>
    intro s base h
    have hne : a ≠ base := by
      have := h 0 (by simp only [List.length_cons]; omega)
      simpa using this
    rw [MachineState.writeWords_cons, ih (s.setMem base w) (base + 8) ?tail]
    case tail =>
      intro k hk
      have := h (k + 1) (by simp only [List.length_cons]; omega)
      rwa [addr_succ] at this
    simp [MachineState.getMem, MachineState.setMem, hne]

/-- A cell inside the block reads back the word written there. -/
theorem getMem_writeWords_hit : ∀ (ws : List Word) (s : MachineState) (base : Word) (k : Nat) (w : Word),
    ws[k]? = some w → base.toNat + 8 * ws.length < 2 ^ 64 →
    (s.writeWords base ws).getMem (base + BitVec.ofNat 64 (8 * k)) = w := by
  intro ws
  induction ws with
  | nil => intro s base k w h _; simp at h
  | cons w0 ws ih =>
    intro s base k w hk hb
    simp only [List.length_cons] at hb
    match k with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      rw [show base + BitVec.ofNat 64 (8 * 0) = base by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mul_zero, Nat.zero_mod, Nat.add_zero]
        exact Nat.mod_eq_of_lt base.isLt]
      rw [MachineState.writeWords_cons, getMem_writeWords_miss _ ws _ (base + 8) ?tail]
      case tail =>
        refine block_ne _ _ _ ?_ ?_ <;>
          simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow] <;> omega
      simp [MachineState.getMem, MachineState.setMem]
    | k + 1 =>
      simp only [List.getElem?_cons_succ] at hk
      rw [MachineState.writeWords_cons, addr_succ]
      refine ih (s.setMem base w0) (base + 8) k w hk ?_
      simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
      omega

/-! ### Indexing the digest blocks -/

theorem digestWordsFlat_length (ds : List Digest) : (ds.flatMap digestWords).length = 2 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.length_append, ih, digestWords, List.length_cons,
      List.length_nil]
    omega

theorem digestWordsFlat_lo : ∀ (ds : List Digest) (i : Nat) (hi : i < ds.length),
    (ds.flatMap digestWords)[2 * i]? = some (dLo ds[i]) := by
  intro ds
  induction ds with
  | nil => intro i hi; simp at hi
  | cons d ds ih =>
    intro i hi
    match i with
    | 0 => rfl
    | i + 1 =>
      simp only [List.length_cons] at hi
      have h := ih i (by omega)
      simp only [List.flatMap_cons, digestWords, List.cons_append, List.nil_append,
        show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getElem?_cons_succ, List.getElem_cons_succ]
      exact h

theorem digestWordsFlat_hi : ∀ (ds : List Digest) (i : Nat) (hi : i < ds.length),
    (ds.flatMap digestWords)[2 * i + 1]? = some (dHi ds[i]) := by
  intro ds
  induction ds with
  | nil => intro i hi; simp at hi
  | cons d ds ih =>
    intro i hi
    match i with
    | 0 => rfl
    | i + 1 =>
      simp only [List.length_cons] at hi
      have h := ih i (by omega)
      simp only [List.flatMap_cons, digestWords, List.cons_append, List.nil_append,
        show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega, List.getElem?_cons_succ,
        List.getElem_cons_succ]
      exact h

/-- The digest at slot `i` of a digest block written by `writeWords`. -/
theorem hasDigest_writeWords (s : MachineState) (base : Word) (n : Nat) (e : Fin n → Digest)
    (hb : base.toNat + 16 * n < 2 ^ 64) (i : Fin n) :
    HasDigest (s.writeWords base ((List.ofFn e).flatMap digestWords))
      (base + BitVec.ofNat 64 (16 * i.val)) (e i) := by
  have hlen : ((List.ofFn e).flatMap digestWords).length = 2 * n := by
    rw [digestWordsFlat_length, List.length_ofFn]
  have hb' : base.toNat + 8 * ((List.ofFn e).flatMap digestWords).length < 2 ^ 64 := by
    rw [hlen]; omega
  have hi : i.val < (List.ofFn e).length := by rw [List.length_ofFn]; exact i.isLt
  constructor
  · rw [show 16 * i.val = 8 * (2 * i.val) by omega]
    refine getMem_writeWords_hit _ s base (2 * i.val) _ ?_ hb'
    rw [digestWordsFlat_lo (List.ofFn e) i.val hi, List.getElem_ofFn]
  · rw [show base + BitVec.ofNat 64 (16 * i.val) + 8 = base + BitVec.ofNat 64 (8 * (2 * i.val + 1)) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]
      omega]
    refine getMem_writeWords_hit _ s base (2 * i.val + 1) _ ?_ hb'
    rw [digestWordsFlat_hi (List.ofFn e) i.val hi, List.getElem_ofFn]

/-! ### Peeling the later blocks of `initState`

Each layout block sits above the ones written before it, so a read below a
block's base sees straight through it. -/

theorem getMem_peel (s : MachineState) (base a : Word) (ws : List Word)
    (h : a.toNat < base.toNat) (hb : base.toNat + 8 * ws.length < 2 ^ 64) :
    (s.writeWords base ws).getMem a = s.getMem a :=
  getMem_writeWords_miss a ws s base (block_ne a base ws.length hb (Or.inl h))

theorem getMem_peel_digests (s : MachineState) (base a : Word) (n : Nat) (e : Fin n → Digest)
    (h : a.toNat < base.toNat) (hb : base.toNat + 16 * n < 2 ^ 64) :
    (s.writeWords base ((List.ofFn e).flatMap digestWords)).getMem a = s.getMem a := by
  refine getMem_peel s base a _ h ?_
  rw [digestWordsFlat_length, List.length_ofFn]; omega

theorem peel_auth (s : MachineState) (path : MerkleLevel → Digest) (a : Word)
    (h : a.toNat < 0x10300) :
    (s.writeWords AUTH ((List.ofFn path).flatMap digestWords)).getMem a = s.getMem a :=
  getMem_peel_digests s AUTH a 32 path h (by simp only [AUTH, BitVec.reduceToNat]; omega)

theorem peel_chains (s : MachineState) (cv : ChainIndex → Digest) (a : Word)
    (h : a.toNat < 0x10060) :
    (s.writeWords CHAINS ((List.ofFn cv).flatMap digestWords)).getMem a = s.getMem a :=
  getMem_peel_digests s CHAINS a 42 cv h (by simp only [CHAINS, BitVec.reduceToNat]; omega)

theorem peel_rho (s : MachineState) (ws : List Word) (a : Word) (h : a.toNat < 0x10048)
    (hlen : ws.length = 3) : (s.writeWords RHO ws).getMem a = s.getMem a :=
  getMem_peel s RHO a ws h (by rw [hlen]; simp only [RHO, BitVec.reduceToNat]; omega)

theorem peel_msg (s : MachineState) (ws : List Word) (a : Word) (h : a.toNat < 0x10028)
    (hlen : ws.length = 4) : (s.writeWords MSG ws).getMem a = s.getMem a :=
  getMem_peel s MSG a ws h (by rw [hlen]; simp only [MSG, BitVec.reduceToNat]; omega)

theorem peel_epoch (s : MachineState) (ws : List Word) (a : Word) (h : a.toNat < 0x10020)
    (hlen : ws.length = 1) : (s.writeWords EPOCH ws).getMem a = s.getMem a :=
  getMem_peel s EPOCH a ws h (by rw [hlen]; simp only [EPOCH, BitVec.reduceToNat]; omega)

theorem peel_param (s : MachineState) (ws : List Word) (a : Word) (h : a.toNat < 0x10010)
    (hlen : ws.length = 2) : (s.writeWords PARAM ws).getMem a = s.getMem a :=
  getMem_peel s PARAM a ws h (by rw [hlen]; simp only [PARAM, BitVec.reduceToNat]; omega)

/-! ### `initState` represents its inputs

This is the bridge PLAN E2 asks for: the differential harness builds
`initState`, the correctness theorem assumes `Represents`, and this theorem
says they are the same thing. -/

theorem initState_code (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature) :
    (initState pk ep msg sig).code = verifierCode := by
  simp only [initState, MachineState.code_writeWords, blankState]
  rfl

theorem initState_pc (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature) :
    (initState pk ep msg sig).pc = CODE_BASE := by
  simp only [initState, MachineState.pc_writeWords, blankState]

set_option maxRecDepth 4000 in
/-- The public key, epoch, message and randomness are where the layout says. -/
theorem initState_scalars (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature) :
    HasDigest (initState pk ep msg sig) ROOT pk.root ∧
    HasDigest (initState pk ep msg sig) PARAM pk.parameter ∧
    (initState pk ep msg sig).getMem EPOCH = BitVec.ofNat 64 ep.val ∧
    HasMessage (initState pk ep msg sig) MSG msg ∧
    HasRandomness (initState pk ep msg sig) RHO sig.randomness := by
  unfold initState HasDigest HasMessage HasRandomness
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  all_goals try
    rw [peel_auth _ _ _ (by decide), peel_chains _ _ _ (by decide),
      peel_rho _ _ _ (by decide) rfl, peel_msg _ _ _ (by decide) rfl,
      peel_epoch _ _ _ (by decide) rfl, peel_param _ _ _ (by decide) rfl]
  all_goals try
    rw [peel_auth _ _ _ (by decide), peel_chains _ _ _ (by decide),
      peel_rho _ _ _ (by decide) rfl, peel_msg _ _ _ (by decide) rfl,
      peel_epoch _ _ _ (by decide) rfl]
  all_goals try
    rw [peel_auth _ _ _ (by decide), peel_chains _ _ _ (by decide),
      peel_rho _ _ _ (by decide) rfl, peel_msg _ _ _ (by decide) rfl]
  all_goals try
    rw [peel_auth _ _ _ (by decide), peel_chains _ _ _ (by decide),
      peel_rho _ _ _ (by decide) rfl]
  all_goals try
    rw [peel_auth _ _ _ (by decide), peel_chains _ _ _ (by decide)]
  all_goals
    simp [MachineState.writeWords, MachineState.setMem, MachineState.getMem, digestWords,
      ROOT, PARAM, EPOCH, MSG, RHO]

theorem initState_chains (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature)
    (i : ChainIndex) :
    HasDigest (initState pk ep msg sig) (CHAINS + BitVec.ofNat 64 (16 * i.val)) (sig.chainValue i) := by
  have hi : i.val < 42 := i.isLt
  have hlt : (CHAINS + BitVec.ofNat 64 (16 * i.val)).toNat < 0x10300 := by
    simp only [CHAINS, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]
    omega
  have hlt8 : (CHAINS + BitVec.ofNat 64 (16 * i.val) + 8).toNat < 0x10300 := by
    simp only [CHAINS, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]
    omega
  unfold initState HasDigest
  refine ⟨?_, ?_⟩
  · rw [peel_auth _ _ _ hlt]
    exact (hasDigest_writeWords _ CHAINS 42 sig.chainValue
      (by simp only [CHAINS, BitVec.reduceToNat]; omega) i).1
  · rw [peel_auth _ _ _ hlt8]
    exact (hasDigest_writeWords _ CHAINS 42 sig.chainValue
      (by simp only [CHAINS, BitVec.reduceToNat]; omega) i).2

theorem initState_auth (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature)
    (l : MerkleLevel) :
    HasDigest (initState pk ep msg sig) (AUTH + BitVec.ofNat 64 (16 * l.val)) (sig.authPath l) :=
  hasDigest_writeWords _ AUTH 32 sig.authPath (by simp only [AUTH, BitVec.reduceToNat]; omega) l

/-- **The harness and the theorem agree.** The state the differential harness
    builds from structured inputs satisfies the theorem's precondition. -/
theorem initState_represents (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature) :
    Represents (initState pk ep msg sig) pk ep msg sig :=
  ⟨(initState_scalars pk ep msg sig).1, (initState_scalars pk ep msg sig).2.1,
   (initState_scalars pk ep msg sig).2.2.1, (initState_scalars pk ep msg sig).2.2.2.1,
   (initState_scalars pk ep msg sig).2.2.2.2, initState_chains pk ep msg sig,
   initState_auth pk ep msg sig⟩

end XmssAsm
