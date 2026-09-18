/-
  XmssAsmTests.Regions

  Component-level executable checks (PLAN E3): the byte-level bridge
  (tweaks, payloads, hash inputs) evaluated against the specification's
  functions, and the chain-walk region run in isolation for every digit
  `0..7`, for both implementations, against `recoverChain` under `H_test`,
  with the frame checked on a memory sample and the cycle counts recorded.
-/

import XmssAsmTests.Fixtures
import XmssAsm.Machine.Eval
import XmssAsm.Regions.Chain
import XmssAsm.Regions.Chains
import XmssAsm.Regions.Leaf
import XmssAsm.Regions.Decode
import XmssAsm.Regions.Auth
import XmssAsm.Represent

namespace XmssAsm.Tests

open RiscvZkvm.Rv64 XmssSecurity

/-! ## Byte-level bridge, evaluated -/

def allOnes : Digest := BitVec.allOnes 128

def componentChecks : List (String × Bool) :=
  let g : Rng := ⟨0xC0FFEE⟩
  let (P, g) := g.digest
  let (v, g) := g.digest
  let (l, g) := g.digest
  let (r, g) := g.digest
  let (msg, g) := g.message
  let (rho, g) := g.randomness
  let (o1, g) := g.digest
  let (o2, _) := g.digest
  let o : HashOutput := o2 ++ o1
  let e : ChainIndex → Digest := fun i => v ^^^ BitVec.ofNat digestBits i.val
  [("tweak.chain", tweakBytes (.chain (epochOf 5) (ci 3) ⟨2, by decide⟩) == wordsBytes [tw0 1 26, tw1 5]),
   ("tweak.chain.max",
     tweakBytes (.chain (epochOf (lifetime - 1)) (ci 41) ⟨6, by decide⟩) ==
       wordsBytes [tw0 1 (8 * 41 + 6), tw1 (lifetime - 1)]),
   ("tweak.leaf", tweakBytes (.leaf (epochOf 7)) == wordsBytes [tw0 2 0, tw1 7]),
   ("tweak.encoding", tweakBytes (.encoding (epochOf 123456789)) == wordsBytes [tw0 4 0, tw1 123456789]),
   ("tweak.merkle", tweakBytes (.merkle (ml 4) ⟨9, by decide⟩) == wordsBytes [tw0 3 5, tw1 9]),
   ("tweak.merkle.top", tweakBytes (.merkle (ml 31) ⟨0, by decide⟩) == wordsBytes [tw0 3 32, tw1 0]),
   ("payload.encoding",
     Concrete.encodingPayload msg rho ==
       wordsBytes [mW msg 0, mW msg 1, mW msg 2, mW msg 3, rW rho 0, rW rho 1, rW rho 2, 0]),
   ("payload.node", Concrete.nodePayload l r == wordsBytes [dLo l, dHi l, dLo r, dHi r]),
   ("payload.leaf", Concrete.leafPayload e == wordsBytes (digestsWords (List.ofFn e))),
   ("hashInput.chain",
     tweakableHashInput P (.chain (epochOf 77) (ci 12) ⟨3, by decide⟩) (bytesLE 16 v) ==
       wordsBytes [tw0 1 (8 * 12 + 3), tw1 77, dLo P, dHi P, dLo v, dHi v]),
   ("hashInput.leaf",
     tweakableHashInput P (.leaf (epochOf 77)) (Concrete.leafPayload e) ==
       wordsBytes ([tw0 2 0, tw1 77, dLo P, dHi P] ++ digestsWords (List.ofFn e))),
   ("digest.roundtrip", digestOfWords (dLo v) (dHi v) == v),
   ("digest.zero", bytesLE 16 (0 : Digest) == wordsBytes [0, 0]),
   ("truncate.words",
     dLo (truncateHash o) == o.extractLsb' 0 64 && dHi (truncateHash o) == o.extractLsb' 64 64)]

/-! ## Running a region in isolation -/

/-- Step until `pc = target` (`true`), a trap, or the fuel runs out. -/
def runUntil (H : List UInt8 → BitVec 256) :
    Nat → MachineState → Word → Stats → MachineState × Stats × Bool
  | 0, s, _, st => (s, st, false)
  | fuel + 1, s, target, st =>
    if s.pc == target then (s, st, true) else
    match stepH H s with
    | none => (s, st, false)
    | some s' =>
      runUntil H fuel s' target
        { steps := st.steps + 1, hashes := st.hashes + (if isHashCall s then 1 else 0) }


/-- Non-zero, address-dependent memory contents, so that a stray store shows. -/
def sentinelMem (a : Word) : Word := a * 0x9E3779B97F4A7C15#64 + 0x0101010101010101#64

def allRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
   .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- The doubleword cells of the whole data layout. -/
def layoutCells : List Word :=
  (List.range ((SCRATCH_HI.toNat - ROOT.toNat) / 8)).map fun k => ROOT + BitVec.ofNat 64 (8 * k)

/-! ### The executable frame checks

Each is `decide` of the *same* `Prop` the region theorem's `Frame` uses, not a
hand-written copy of it. A copy drifts the first time a candidate changes a
write set, and it drifts silently: the theorem still holds, the mirror still
evaluates, and the suite reports a frame violation that is not there (or, worse,
misses one that is). -/

instance WChain.decidable (a : Word) : Decidable (WChain a) := by
  unfold WChain; infer_instance
instance WChains.decidable (a : Word) : Decidable (WChains a) := by
  unfold WChains; infer_instance
instance WLeaf.decidable (a : Word) : Decidable (WLeaf a) := by
  unfold WLeaf; infer_instance
instance WDecode.decidable (a : Word) : Decidable (WDecode a) := by
  unfold WDecode; infer_instance
instance WAuth.decidable (a : Word) : Decidable (WAuth a) := by
  unfold WAuth; infer_instance

def inWChain (a : Word) : Bool := decide (WChain a)

/-- The entry state of a chain walk: the contract's precondition on top of
    sentinel registers and memory. -/
def chainState (P : PublicParameter) (ep : Epoch) (i : ChainIndex) (x : Digit)
    (v : Digest) : MachineState :=
  let s : MachineState :=
    { regs := fun _ => 0xDEADBEEF#64, mem := sentinelMem, code := verifierCode, pc := addr idxChainWalk }
  let s := (((((s.setReg .x8 (BitVec.ofNat 64 ep.val)).setReg .x14 (BitVec.ofNat 64 x.val)).setReg
    .x16 (BitVec.ofNat 64 (8 * i.val))).setReg .x13 (BitVec.ofNat 64 i.val)).setReg
    .x18 ENDPTS).setReg .x19 DIGITS
  (s.writeWords BUFA_P [dLo P, dHi P]).writeWords CUR [dLo v, dHi v]

def readDigest (s : MachineState) (a : Word) : Digest := digestOfWords (s.getMem a) (s.getMem (a + 8))

structure ChainCase where
  name : String
  P : PublicParameter
  ep : Epoch
  i : ChainIndex
  x : Digit
  v : Digest

/-- Run one chain case on one implementation; `none` on success. -/
def checkChain (c : ChainCase) : Option String × Stats :=
  let s := chainState c.P c.ep c.i c.x c.v
  let (s', st, reached) := runUntil H_test 1000 s (addr idxChainStore) {}
  let expected := evalD (Concrete.recoverChain c.P c.ep c.i c.x c.v)
  let got := readDigest s' CUR
  let keepOk := [Reg.x8, .x13, .x16, .x18, .x19].all fun r => s'.getReg r == s.getReg r
  let clobOk := allRegs.all fun r => CLOB.contains r || s'.getReg r == s.getReg r
  let frameOk := layoutCells.all fun a => inWChain a || s'.getMem a == s.getMem a
  let pOk := readDigest s' BUFA_P == c.P
  let err :=
    if !reached then some s!"{c.name}: did not reach the region end (pc={s'.pc.toNat})"
    else if got != expected then some s!"{c.name}: CUR mismatch"
    else if !pOk then some s!"{c.name}: P clobbered"
    else if !keepOk then some s!"{c.name}: caller register clobbered"
    else if !clobOk then some s!"{c.name}: non-CLOB register written"
    else if !frameOk then some s!"{c.name}: memory outside WChain written"
    else if st.hashes != 7 - c.x.val then some s!"{c.name}: {st.hashes} hashes, expected {7 - c.x.val}"
    else none
  (err, st)

def digit (n : Nat) : Digit := ⟨n % chainLength, Nat.mod_lt _ (by decide)⟩

/-- Every digit, with edge-case and pseudo-random starting digests, epochs and chains. -/
def chainCorpus : List ChainCase := Id.run do
  let mut out : List ChainCase := []
  let mut g : Rng := ⟨0x5EED⟩
  for xn in List.range 8 do
    let x := digit xn
    let (P, g1) := g.digest
    let (ep, g2) := g1.epoch
    let (i, g3) := g2.next
    let ir : ChainIndex := ⟨i.toNat % numChains, Nat.mod_lt _ (by decide)⟩
    let (v1, g4) := g3.digest
    let (v2, g5) := g4.digest
    let (v3, g6) := g5.digest
    g := g6
    let edges : List (String × Digest) :=
      [("zero", 0), ("ones", allOnes), ("one", 1), ("msb", 1 <<< 127), ("rnd1", v1), ("rnd2", v2), ("rnd3", v3)]
    let envs : List (String × Epoch × ChainIndex) :=
      [("ep0.c0", epochOf 0, ci 0), ("epMax.c41", epochOf (lifetime - 1), ci 41), ("epR.cR", ep, ir)]
    for (vn, v) in edges do
      for (en, e, c) in envs do
        out := out ++ [⟨s!"chain.x{xn}.{vn}.{en}", P, e, c, x, v⟩]
  return out

/-- Steps and hashes per digit for one implementation (starting digest zero, epoch 0, chain 0). -/
def chainCycles : List (Nat × Stats) :=
  (List.range 8).map fun xn =>
    let c : ChainCase := ⟨"", 0, epochOf 0, ci 0, digit xn, 0⟩
    (xn, (checkChain c).2)

/-! ## The chains region and the leaf region in isolation -/


def inWChains (a : Word) : Bool := decide (WChains a)

def inWLeaf (a : Word) : Bool := decide (WLeaf a)

structure ChainsCase where
  name : String
  P : PublicParameter
  ep : Epoch
  cv : ChainIndex → Digest
  enc : Encoding

def chainsState (c : ChainsCase) : MachineState :=
  let s : MachineState :=
    { regs := fun _ => 0xDEADBEEF#64, mem := sentinelMem, code := verifierCode, pc := addr idxChains }
  let s := s.setReg .x8 (BitVec.ofNat 64 c.ep.val)
  let s := s.writeWords BUFA_P [dLo c.P, dHi c.P]
  let s := s.writeWords CHAINS ((List.ofFn c.cv).flatMap digestWords)
  s.writeWords DIGITS ((List.ofFn c.enc).map fun d => BitVec.ofNat 64 d.val)

/-- Run the chains region on a build; `none` on success. -/
def checkChains (c : ChainsCase) : Option String × Stats :=
  let s := chainsState c
  let (s', st, reached) := runUntil H_test 20000 s (addr idxLeaf) {}
  let endOk := (List.range numChains).all fun j =>
    let jj : ChainIndex := ⟨j % numChains, Nat.mod_lt _ (by decide)⟩
    readDigest s' (ENDPTS + BitVec.ofNat 64 (16 * j)) ==
      evalD (Concrete.recoverChain c.P c.ep jj (c.enc jj) (c.cv jj))
  let keepOk := s'.getReg .x8 == s.getReg .x8
  let clobOk := allRegs.all fun r => CLOB.contains r || s'.getReg r == s.getReg r
  let frameOk := layoutCells.all fun a => inWChains a || s'.getMem a == s.getMem a
  let expectedHashes := (List.range numChains).foldl (fun acc j =>
    acc + (7 - (c.enc ⟨j % numChains, Nat.mod_lt _ (by decide)⟩).val)) 0
  let err :=
    if !reached then some s!"{c.name}: chains did not reach idxLeaf (pc={s'.pc.toNat})"
    else if !endOk then some s!"{c.name}: endpoint mismatch"
    else if !keepOk then some s!"{c.name}: x8 clobbered"
    else if !clobOk then some s!"{c.name}: non-CLOB register written"
    else if !frameOk then some s!"{c.name}: memory outside WChains written"
    else if st.hashes != expectedHashes then some s!"{c.name}: {st.hashes} hashes, expected {expectedHashes}"
    else none
  (err, st)

def constEnc (d : Nat) : Encoding := fun _ => digit d

def Rng.encoding (g : Rng) : Encoding × Rng := Id.run do
  let mut g := g
  let mut ds : List Nat := []
  for _ in List.range numChains do
    let (x, g') := g.next
    g := g'
    ds := ds ++ [x.toNat % 8]
  return (fun i => digit (ds.getD i.val 0), g)

def chainsCorpus : List ChainsCase := Id.run do
  let mut out : List ChainsCase := []
  let mut g : Rng := ⟨0xC4A1⟩
  for k in List.range 3 do
    let (P, g1) := g.digest
    let (ep, g2) := g1.epoch
    let (cvs, g3) := g2.digests numChains
    let (enc, g4) := g3.encoding
    g := g4
    let cv := ofList cvs numChains
    let e := if k == 0 then epochOf 0 else if k == 1 then epochOf (lifetime - 1) else ep
    out := out ++ [⟨s!"chains.rnd{k}", P, e, cv, enc⟩, ⟨s!"chains.all0.{k}", P, e, cv, constEnc 0⟩,
      ⟨s!"chains.all7.{k}", P, e, cv, constEnc 7⟩]
  return out

structure LeafCase where
  name : String
  P : PublicParameter
  ep : Epoch
  e : ChainIndex → Digest

def leafState (c : LeafCase) : MachineState :=
  let s : MachineState :=
    { regs := fun _ => 0xDEADBEEF#64, mem := sentinelMem, code := verifierCode, pc := addr idxLeaf }
  let s := s.setReg .x8 (BitVec.ofNat 64 c.ep.val)
  let s := s.writeWords BUFL_P [dLo c.P, dHi c.P]
  s.writeWords ENDPTS ((List.ofFn c.e).flatMap digestWords)

def checkLeaf (c : LeafCase) : Option String × Stats :=
  let s := leafState c
  let (s', st, reached) := runUntil H_test 1000 s (addr idxAuth) {}
  let got := readDigest s' CUR
  let expected := evalD (Concrete.leafHash c.P c.ep c.e)
  let keepOk := s'.getReg .x8 == s.getReg .x8
  let clobOk := allRegs.all fun r => CLOB.contains r || s'.getReg r == s.getReg r
  let frameOk := layoutCells.all fun a => inWLeaf a || s'.getMem a == s.getMem a
  let err :=
    if !reached then some s!"{c.name}: leaf did not reach idxAuth (pc={s'.pc.toNat})"
    else if got != expected then some s!"{c.name}: leaf mismatch"
    else if !keepOk then some s!"{c.name}: x8 clobbered"
    else if !clobOk then some s!"{c.name}: non-CLOB register written"
    else if !frameOk then some s!"{c.name}: memory outside WLeaf written"
    else if st.hashes != 1 then some s!"{c.name}: {st.hashes} hashes, expected 1"
    else none
  (err, st)

def leafCorpus : List LeafCase := Id.run do
  let mut out : List LeafCase := []
  let mut g : Rng := ⟨0x1EAF⟩
  for k in List.range 3 do
    let (P, g1) := g.digest
    let (ep, g2) := g1.epoch
    let (es, g3) := g2.digests numChains
    g := g3
    let e := if k == 0 then epochOf 0 else if k == 1 then epochOf (lifetime - 1) else ep
    out := out ++ [⟨s!"leaf.rnd{k}", P, e, ofList es numChains⟩]
  out := out ++ [⟨"leaf.zero", 0, epochOf 5, fun _ => 0⟩, ⟨"leaf.ones", allOnes, epochOf 5, fun _ => allOnes⟩]
  return out

/-! ## The decode region in isolation -/

/-- A digest with the given 42 digits at the layout's offsets (padding bits clear). -/
def digestOfDigits (f : Nat → Nat) : Digest :=
  (List.range 42).foldl (fun (acc : BitVec 128) i =>
    acc ||| (BitVec.ofNat 128 (f i % 8) <<< (3 * i + if i < 21 then 0 else 1))) (0 : BitVec 128)

/-- `d` with bit `b` set. -/
def setBit (d : Digest) (b : Nat) : Digest := d ||| ((1 : Digest) <<< b)

structure DecodeCase where
  name : String
  d : Digest

def decodeState (c : DecodeCase) : MachineState :=
  let s : MachineState :=
    { regs := fun _ => 0xDEADBEEF#64, mem := sentinelMem, code := verifierCode, pc := addr idxDecode }
  (s.setReg .x20 (dLo c.d)).setReg .x21 (dHi c.d)

def inWDecode (a : Word) : Bool := decide (WDecode a)

/-- Run decode until it either reaches `idxChains` or halts. -/
def runDecode (s : MachineState) : MachineState × Stats × Bool × Bool := Id.run do
  let (s', st, reached) := runUntil H_test 1000 s (addr idxChains) {}
  if reached then return (s', st, true, false)
  -- not reached: it must have stopped at a halt
  return (s', st, false, isHalted s')

def checkDecode (c : DecodeCase) : Option String × Stats :=
  let s := decodeState c
  let (s', st, accepted, halted) := runDecode s
  let frameOk := layoutCells.all fun a => inWDecode a || s'.getMem a == s.getMem a
  let clobOk := allRegs.all fun r => CLOB.contains r || s'.getReg r == s.getReg r
  let x8Ok := s'.getReg .x8 == s.getReg .x8
  let err :=
    match TargetSum.decodeDigest c.d with
    | some enc =>
      let digitsOk := (List.range numChains).all fun j =>
        s'.getMem (DIGITS + BitVec.ofNat 64 (8 * j)) ==
          BitVec.ofNat 64 (enc ⟨j % numChains, Nat.mod_lt _ (by decide)⟩).val
      if !accepted then some s!"{c.name}: spec accepts, machine did not reach idxChains"
      else if !digitsOk then some s!"{c.name}: digit mismatch"
      else none
    | none =>
      if accepted then some s!"{c.name}: spec rejects, machine continued"
      else if !halted then some s!"{c.name}: spec rejects, machine did not halt (pc={s'.pc.toNat})"
      else if s'.getReg .x10 != 0 then some s!"{c.name}: reject with a0={(s'.getReg .x10).toNat}"
      else none
  let err := err <|> (if !frameOk then some s!"{c.name}: memory outside DIGITS written"
    else if !clobOk then some s!"{c.name}: non-CLOB register written"
    else if !x8Ok then some s!"{c.name}: x8 clobbered" else none)
  (err, st)

/-- Digits summing to 195: 27 fives and 15 fours. -/
def digits195 (i : Nat) : Nat := if i < 27 then 5 else 4
def digits194 (i : Nat) : Nat := if i == 0 then 4 else digits195 i
def digits196 (i : Nat) : Nat := if i == 41 then 5 else digits195 i
/-- 195 with the extreme digits 7 and 0: 27 sevens, 6 ones, 9 zeros. -/
def digitsEdge (i : Nat) : Nat := if i < 27 then 7 else if i < 33 then 1 else 0

def decodeCorpus : List DecodeCase := Id.run do
  let d195 := digestOfDigits digits195
  let dEdge := digestOfDigits digitsEdge
  let mut out : List DecodeCase :=
    [⟨"decode.sum195", d195⟩, ⟨"decode.sum195.edge", dEdge⟩,
     ⟨"decode.sum194", digestOfDigits digits194⟩, ⟨"decode.sum196", digestOfDigits digits196⟩,
     ⟨"decode.sum195.bit63", setBit d195 63⟩, ⟨"decode.sum195.bit127", setBit d195 127⟩,
     ⟨"decode.sum195.bits63.127", setBit (setBit d195 63) 127⟩,
     ⟨"decode.zero", 0⟩, ⟨"decode.ones", allOnes⟩, ⟨"decode.all7", digestOfDigits fun _ => 7⟩,
     ⟨"decode.all4", digestOfDigits fun _ => 4⟩]
  let mut g : Rng := ⟨0xDEC0DE⟩
  for k in List.range 6 do
    let (d, g') := g.digest
    g := g'
    out := out ++ [⟨s!"decode.rnd{k}", d⟩]
  -- the encoding digests of the valid end-to-end fixtures (accepting)
  for f in corpus do
    if f.name.startsWith "valid-" && !(f.name.any (· == '/')) then
      out := out ++ [⟨s!"decode.{f.name}", evalD (Concrete.encodingHash f.pk.parameter f.ep f.msg f.sig.randomness)⟩]
  return out

/-! ## The auth region in isolation -/

structure AuthCase where
  name : String
  P : PublicParameter
  ep : Epoch
  path : MerkleLevel → Digest
  leaf : Digest

def authState (c : AuthCase) : MachineState :=
  let s : MachineState :=
    { regs := fun _ => 0xDEADBEEF#64, mem := sentinelMem, code := verifierCode, pc := addr idxAuth }
  let s := s.setReg .x8 (BitVec.ofNat 64 c.ep.val)
  let s := s.writeWords BUFA_P [dLo c.P, dHi c.P]
  let s := s.writeWords CUR [dLo c.leaf, dHi c.leaf]
  s.writeWords AUTH ((List.ofFn c.path).flatMap digestWords)

def inWAuth (a : Word) : Bool := decide (WAuth a)

def checkAuth (c : AuthCase) : Option String × Stats :=
  let s := authState c
  let (s', st, reached) := runUntil H_test 5000 s (addr idxFinal) {}
  let sig : Signature := ⟨0, fun _ => 0, c.path⟩
  let expected := evalD (Concrete.authenticationRoot c.P c.ep sig treeHeight c.leaf)
  let got := readDigest s' CUR
  let clobOk := allRegs.all fun r => CLOB.contains r || s'.getReg r == s.getReg r
  let frameOk := layoutCells.all fun a => inWAuth a || s'.getMem a == s.getMem a
  let err :=
    if !reached then some s!"{c.name}: auth did not reach idxFinal (pc={s'.pc.toNat})"
    else if got != expected then some s!"{c.name}: root mismatch"
    else if !clobOk then some s!"{c.name}: non-CLOB register written"
    else if !frameOk then some s!"{c.name}: memory outside WAuth written"
    else if st.hashes != 32 then some s!"{c.name}: {st.hashes} hashes, expected 32"
    else none
  (err, st)

/-- Epochs exercising both child orderings at every level: all bits clear, all
    set, alternating patterns, and pseudo-random. -/
def authCorpus : List AuthCase := Id.run do
  let mut out : List AuthCase := []
  let mut g : Rng := ⟨0xA07⟩
  let epochs : List (String × Epoch) :=
    [("ep0", epochOf 0), ("epMax", epochOf (lifetime - 1)), ("ep0x5555", epochOf 0x55555555),
     ("ep0xAAAA", epochOf 0xAAAAAAAA), ("ep1", epochOf 1), ("ep2^31", epochOf (2 ^ 31))]
  for (en, ep) in epochs do
    let (P, g1) := g.digest
    let (ps, g2) := g1.digests treeHeight
    let (leaf, g3) := g2.digest
    g := g3
    out := out ++ [⟨s!"auth.{en}", P, ep, ofList ps treeHeight, leaf⟩]
  for k in List.range 3 do
    let (P, g1) := g.digest
    let (ep, g2) := g1.epoch
    let (ps, g3) := g2.digests treeHeight
    let (leaf, g4) := g3.digest
    g := g4
    out := out ++ [⟨s!"auth.rnd{k}", P, ep, ofList ps treeHeight, leaf⟩]
  out := out ++ [⟨"auth.zero", 0, epochOf 7, fun _ => 0, 0⟩, ⟨"auth.ones", allOnes, epochOf 7, fun _ => allOnes, allOnes⟩]
  return out

end XmssAsm.Tests
