/-
  XmssAsmTests.Fixtures

  Deterministic structured inputs. Valid fixtures are built from the
  specification's own algorithms under `H_test`: random chain starts walked
  with `chainWalk`, the leaf from `leafHash`, and a root folded from random
  authentication nodes with `authenticationRoot`, so `Concrete.verify`
  accepts by construction. Invalid fixtures are mutations of valid ones and
  simple edge cases; the expected result is always whatever the spec says.
-/

import XmssAsmTests.TestHash
import XmssAsm.Spec.Eval

namespace XmssAsm.Tests

open XmssSecurity OracleComp

/-- splitmix64. -/
structure Rng where
  state : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  (fin64 s, ⟨s⟩)

def Rng.word (g : Rng) : BitVec 64 × Rng :=
  let (x, g) := g.next; (x.toBitVec, g)

def Rng.digest (g : Rng) : Digest × Rng :=
  let (lo, g) := g.word
  let (hi, g) := g.word
  (hi ++ lo, g)

def Rng.message (g : Rng) : Message × Rng :=
  let (a, g) := g.digest
  let (b, g) := g.digest
  (b ++ a, g)

def Rng.randomness (g : Rng) : Randomness × Rng :=
  let (a, g) := g.digest
  let (b, g) := g.word
  (b ++ a, g)

def Rng.epoch (g : Rng) : Epoch × Rng :=
  let (x, g) := g.next
  (⟨(x.toNat % lifetime), Nat.mod_lt _ (by decide)⟩, g)

def Rng.digests (g : Rng) : Nat → List Digest × Rng
  | 0 => ([], g)
  | n + 1 =>
    let (d, g) := g.digest
    let (ds, g) := g.digests n
    (d :: ds, g)

def ofList (l : List Digest) (n : Nat) : Fin n → Digest := fun i => l.getD i.val 0

/-- One structured verifier input. -/
structure Fixture where
  name : String
  pk : PublicKey
  ep : Epoch
  msg : Message
  sig : Signature

/-- The expected result: the specification evaluated under `H_test`, in the
    evaluable form `specVerify` (equal to `Concrete.verify` by `specVerify_eq`). -/
def Fixture.expected (f : Fixture) : Bool := specVerify H_test f.pk f.ep f.msg f.sig

def evalD (oa : OracleComp HashSpec Digest) : Digest := evalH H_test oa

/-- Search the randomness for an encodable digest (target sum 195, padding
    bits clear). Returns the randomness and encoding, or none after `tries`. -/
partial def findEncoding (P : PublicParameter) (ep : Epoch) (msg : Message) (g : Rng) (tries : Nat) :
    Option (Randomness × Encoding × Rng) :=
  if tries = 0 then none else
  let (rho, g) := g.randomness
  let d := evalD (Concrete.encodingHash P ep msg rho)
  match TargetSum.decodeDigest d with
  | some enc => some (rho, enc, g)
  | none => findEncoding P ep msg g (tries - 1)

/-- A valid fixture from a seed: accepted by `Concrete.verify` by construction. -/
def validFixture (name : String) (seed : UInt64) (epOverride : Option Epoch := none) :
    Option Fixture :=
  let g : Rng := ⟨seed⟩
  let (P, g) := g.digest
  let (ep0, g) := g.epoch
  let ep := epOverride.getD ep0
  let (msg, g) := g.message
  let (starts, g) := g.digests numChains
  let start := ofList starts numChains
  match findEncoding P ep msg g 100000 with
  | none => none
  | some (rho, enc, g) =>
    let chainValue : ChainIndex → Digest := fun i =>
      evalD (Concrete.chainWalk P ep i 0 (enc i).val (start i))
    let endpoints : ChainIndex → Digest := fun i =>
      evalD (Concrete.chainWalk P ep i 0 (chainLength - 1) (start i))
    let leaf := evalD (Concrete.leafHash P ep endpoints)
    let (nodes, _) := g.digests treeHeight
    let sig : Signature := ⟨rho, chainValue, ofList nodes treeHeight⟩
    let root := evalD (Concrete.authenticationRoot P ep sig treeHeight leaf)
    some ⟨name, ⟨root, P⟩, ep, msg, sig⟩

/-! ## Mutations -/

def flipBit (d : Digest) (k : Nat) : Digest := d ^^^ (1 <<< k)

def Fixture.withRoot (f : Fixture) (r : Digest) : Fixture := { f with pk := { f.pk with root := r } }
def Fixture.withParam (f : Fixture) (p : PublicParameter) : Fixture :=
  { f with pk := { f.pk with parameter := p } }
def Fixture.withMsg (f : Fixture) (m : Message) : Fixture := { f with msg := m }
def Fixture.withEpoch (f : Fixture) (e : Epoch) : Fixture := { f with ep := e }
def Fixture.withChain (f : Fixture) (i : ChainIndex) (d : Digest) : Fixture :=
  { f with sig := { f.sig with chainValue := fun j => if j = i then d else f.sig.chainValue j } }
def Fixture.withAuth (f : Fixture) (l : MerkleLevel) (d : Digest) : Fixture :=
  { f with sig := { f.sig with authPath := fun j => if j = l then d else f.sig.authPath j } }
def Fixture.withRandomness (f : Fixture) (r : Randomness) : Fixture :=
  { f with sig := { f.sig with randomness := r } }
def Fixture.named (f : Fixture) (n : String) : Fixture := { f with name := n }

def epochOf (n : Nat) (h : n < lifetime := by decide) : Epoch := ⟨n, h⟩
def ci (n : Nat) (h : n < numChains := by decide) : ChainIndex := ⟨n, h⟩
def ml (n : Nat) (h : n < treeHeight := by decide) : MerkleLevel := ⟨n, h⟩

/-- The end-to-end corpus. -/
def corpus : List Fixture := Id.run do
  let mut out : List Fixture := []
  -- zero-heavy edge case: everything zero (the spec decides; almost surely rejects)
  out := out ++ [⟨"all-zero", ⟨0, 0⟩, epochOf 0, 0, ⟨0, fun _ => 0, fun _ => 0⟩⟩]
  out := out ++ [⟨"all-ones-digests", ⟨BitVec.allOnes _, BitVec.allOnes _⟩, epochOf (lifetime - 1),
    BitVec.allOnes _, ⟨BitVec.allOnes _, fun _ => BitVec.allOnes _, fun _ => BitVec.allOnes _⟩⟩]
  -- valid fixtures at boundary epochs and random epochs
  let seeds : List (String × UInt64 × Option Epoch) :=
    [("valid-ep0", 1, some (epochOf 0)),
     ("valid-epmax", 2, some (epochOf (lifetime - 1))),
     ("valid-ep1", 3, some (epochOf 1)),
     ("valid-ep2^31", 4, some (epochOf (2 ^ 31))),
     ("valid-rand-a", 5, none), ("valid-rand-b", 6, none), ("valid-rand-c", 7, none),
     ("valid-rand-d", 8, none)]
  for (n, seed, e) in seeds do
    match validFixture n seed e with
    | some f =>
      out := out ++ [f]
      -- mutations of this valid fixture
      out := out ++ [(f.withRoot (flipBit f.pk.root 0)).named (n ++ "/root-bit0"),
                     (f.withRoot (flipBit f.pk.root 127)).named (n ++ "/root-bit127"),
                     (f.withParam (flipBit f.pk.parameter 5)).named (n ++ "/param-bit5"),
                     (f.withMsg (f.msg ^^^ 1)).named (n ++ "/msg-bit0"),
                     (f.withEpoch (epochOf ((f.ep.val + 1) % lifetime) (Nat.mod_lt _ (by decide)))).named
                       (n ++ "/epoch+1"),
                     (f.withChain (ci 0) (flipBit (f.sig.chainValue (ci 0)) 3)).named (n ++ "/chain0-bit3"),
                     (f.withChain (ci 41) (flipBit (f.sig.chainValue (ci 41)) 70)).named (n ++ "/chain41-bit70"),
                     (f.withChain (ci 20) 0).named (n ++ "/chain20-zero"),
                     (f.withAuth (ml 0) (flipBit (f.sig.authPath (ml 0)) 1)).named (n ++ "/auth0-bit1"),
                     (f.withAuth (ml 31) (flipBit (f.sig.authPath (ml 31)) 64)).named (n ++ "/auth31-bit64"),
                     (f.withRandomness (f.sig.randomness ^^^ 1)).named (n ++ "/rho-bit0")]
    | none => pure ()
  -- deterministic pseudo-random junk inputs (the spec decides)
  for k in [0:6] do
    let g : Rng := ⟨1000 + k.toUInt64⟩
    let (P, g) := g.digest
    let (root, g) := g.digest
    let (ep, g) := g.epoch
    let (msg, g) := g.message
    let (rho, g) := g.randomness
    let (cs, g) := g.digests numChains
    let (as, _) := g.digests treeHeight
    out := out ++ [⟨s!"random-{k}", ⟨root, P⟩, ep, msg, ⟨rho, ofList cs numChains, ofList as treeHeight⟩⟩]
  return out

end XmssAsm.Tests
