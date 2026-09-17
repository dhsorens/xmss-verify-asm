/-
  XmssAsm.Contract

  The machine/specification contract (M1): the statement of
  `xmss_verify_correct`, fixed here and discharged in `XmssAsm.Verify` (M7).

  For every hash `H`, every structured input `(pk, ep, msg, sig)`, and every
  machine state whose code is the verifier and whose memory represents the
  input, running the hash-oracle machine from `CODE_BASE`

    * terminates at a `HALT` syscall (`Decomp.SyscallHalted`, and the stepper
      really stops there),
    * with `a0` equal to `Concrete.verify pk ep msg sig` evaluated with every
      oracle query answered by `H` (`1` for `true`, `0` for `false`),
    * having written only the scratch region and only the registers in
      `CLOB`, and having left code and the host-I/O fields untouched.

  The statement is a `Prop`-valued definition rather than a theorem with a
  `sorry`, so the axiom gate stays green while the proof is being built; the
  theorem `xmss_verify_correct : ∀ H, VerifierCorrect H` is the M7 deliverable.

  What the precondition does *not* say, on purpose: nothing about scratch
  memory, registers (`x0` aside), or the `committed`/`publicValues`/
  `privateInput` streams, so the result cannot depend on them. What it does
  say beyond the representation: the code map is exactly `verifierCode`, i.e.
  the whole code memory is the verifier. That is the "program loaded" condition
  and the only way `verifier` enters the statement.

  Legacy file: it names `XmssSecurity.Concrete.verify`.
-/

import XmssAsm.Represent
import XmssAsm.Spec.Eval

namespace XmssAsm

open RiscvZkvm.Rv64 XmssSecurity OracleComp

/-- The boolean result, as the machine reports it in `a0`. -/
def resultWord (b : Bool) : Word := if b then 1 else 0

/-- The correctness contract of the verifier at hash `H`. -/
def VerifierCorrect (H : HashInput → HashOutput) : Prop :=
  ∀ (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature) (s : MachineState),
    s.code = verifierCode → s.pc = CODE_BASE → Represents s pk ep msg sig →
    ∃ s', Reaches H s s' ∧
      Decomp.SyscallHalted s' ∧ stepH H s' = none ∧
      s'.getReg .x10 = resultWord (evalH H (Concrete.verify pk ep msg sig : OracleComp HashSpec Bool)) ∧
      Frame InScratch s s'

end XmssAsm
