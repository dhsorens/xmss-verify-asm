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

end XmssAsm
