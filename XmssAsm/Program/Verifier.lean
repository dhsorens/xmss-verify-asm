/-
  XmssAsm.Program.Verifier

  The RV64 XMSS verifier, as `Program` literals. This is the artifact: the
  correctness theorem is about `verifier`, and the evaluator executes the very
  same value (`XmssAsm.Machine.Eval`), so there is one canonical program.

  Layout of the code (see `XmssAsm.Machine.Layout` for the data):

      init      copy P into both hash buffers, build the encoding payload,
                hash it, load the digest into x20/x21
      decode    padding bits, 21 iterations extracting two digits each,
                target-sum check; on failure halt with a0 = 0
      chains    42 iterations: load chain value into CUR, walk the chain
                (`chainWalk`, the swappable region), store the endpoint
      leaf      hash tweak ‖ P ‖ endpoints into CUR
      auth      32 iterations of the authentication step
      final     compare CUR with pk.root, halt with a0 = 1 or 0

  Register conventions:

      x5 syscall id      x10 x11 x12 hash args      x6 x7 x28..x31 temporaries
      x8 epoch           x13 chain index i          x14 digit x
      x15 chain position x16 8·i                    x17 constant 7
      x18 endpoint ptr   x19 digit ptr              x20 x21 digest lo/hi
      x22 digit sum      x23 x24 decode ptrs        x25 auth level  x26 auth ptr

  Branch offsets are computed from the lists themselves, so swapping the
  chain-walk implementation (M3) moves every later address consistently.
-/

module

public import XmssAsm.Machine.Layout
public import XmssAsm.Machine.Hash

@[expose] public section

namespace XmssAsm

open RiscvZkvm.Rv64

/-! ## Assembler helpers -/

def imm (n : Int) : BitVec 12 := BitVec.ofInt 12 n
def bOff (n : Int) : BitVec 13 := BitVec.ofInt 13 n
def jOff (n : Int) : BitVec 21 := BitVec.ofInt 21 n

/-- Halt with `a0 = v`. -/
def haltWith (v : Word) : Program := [.LI .x10 v, .LI .x5 0, .ECALL]

/-! ## init -/

/-- Copy `P` (16 bytes) into both hash buffers. -/
def initP : Program :=
  [.LI .x6 PARAM, .LD .x7 .x6 0, .LD .x28 .x6 8,
   .LI .x6 BUFA_P, .SD .x6 .x7 0, .SD .x6 .x28 8,
   .LI .x6 BUFL_P, .SD .x6 .x7 0, .SD .x6 .x28 8]

/-- The encoding payload `m ‖ ρ ‖ 0^8` into the payload slot of `BUFA`. -/
def initPayload : Program :=
  [.LI .x6 MSG, .LD .x7 .x6 0, .LD .x28 .x6 8, .LD .x29 .x6 16, .LD .x30 .x6 24,
   .LI .x6 CUR, .SD .x6 .x7 0, .SD .x6 .x28 8, .SD .x6 .x29 16, .SD .x6 .x30 24,
   .LI .x6 RHO, .LD .x7 .x6 0, .LD .x28 .x6 8, .LD .x29 .x6 16,
   .LI .x6 CUR, .SD .x6 .x7 32, .SD .x6 .x28 40, .SD .x6 .x29 48, .SD .x6 .x0 56]

/-- Load the epoch, write the encoding tweak, hash, load the digest. -/
def initHash : Program :=
  [.LI .x6 EPOCH, .LD .x8 .x6 0,
   .LI .x7 0x400, .LI .x6 BUFA, .SD .x6 .x7 0,
   .SLLI .x7 .x8 32, .SD .x6 .x7 8,
   .LI .x5 HASH_ID, .LI .x10 BUFA, .LI .x11 96, .LI .x12 OUT, .ECALL,
   .LI .x6 OUT, .LD .x20 .x6 0, .LD .x21 .x6 8]

def init : Program := initP ++ initPayload ++ initHash

/-! ## decode -/

/-- Padding-bit checks and loop setup. Branches to the local reject stub. -/
def decodePre : Program :=
  [.SRLI .x6 .x20 63, .BNE .x6 .x0 (bOff 84),
   .SRLI .x6 .x21 63, .BNE .x6 .x0 (bOff 76),
   .LI .x22 0, .LI .x23 DIGITS, .LI .x24 (DIGITS + 168), .MV .x6 .x20, .MV .x7 .x21]

/-- One iteration: digit `j` from the low word, digit `21 + j` from the high
    word, both stored and summed. -/
def decodeBody : Program :=
  [.ANDI .x28 .x6 7, .SD .x23 .x28 0, .ADD .x22 .x22 .x28,
   .ANDI .x28 .x7 7, .SD .x23 .x28 168, .ADD .x22 .x22 .x28,
   .SRLI .x6 .x6 3, .SRLI .x7 .x7 3, .ADDI .x23 .x23 8]

def decodeLoop : Program := decodeBody ++ [.BNE .x23 .x24 (bOff (-(4 * decodeBody.length)))]

def decodePost : Program :=
  [.LI .x6 195, .BNE .x22 .x6 (bOff 8), .JAL .x0 (jOff 16)] ++ haltWith 0

def decode : Program := decodePre ++ decodeLoop ++ decodePost

/-! ## chains -/

def chainsPre : Program := [.LI .x13 0, .LI .x18 ENDPTS, .LI .x19 DIGITS, .LI .x16 0]

/-- Load `sig.chainValue i` into `CUR` and the digit into `x14`. -/
def chainLoad : Program :=
  [.LI .x6 CHAINS, .SLLI .x7 .x13 4, .ADD .x6 .x6 .x7, .LD .x28 .x6 0, .LD .x29 .x6 8,
   .LI .x6 CUR, .SD .x6 .x28 0, .SD .x6 .x29 8, .LD .x14 .x19 0]

/-- Implementation A of the chain walk: header-guarded loop, every constant
    reloaded per step. Precondition: `x8 = ep`, `x14 = x`, `x16 = 8 i`, `CUR`
    holds the value. Postcondition: `CUR` holds the walked value. -/
def chainStepA : Program :=
  [.ADD .x6 .x16 .x15, .SLLI .x6 .x6 32, .ADDI .x6 .x6 0x100,
   .LI .x7 BUFA, .SD .x7 .x6 0, .SLLI .x6 .x8 32, .SD .x7 .x6 8,
   .LI .x5 HASH_ID, .LI .x10 BUFA, .LI .x11 48, .LI .x12 OUT, .ECALL,
   .LI .x6 OUT, .LD .x28 .x6 0, .LD .x29 .x6 8, .SD .x7 .x28 32, .SD .x7 .x29 40,
   .ADDI .x15 .x15 1]

def chainWalkA : Program :=
  [.MV .x15 .x14, .LI .x17 7,
   .BGE .x15 .x17 (bOff (4 * (chainStepA.length + 2)))] ++
  chainStepA ++ [.JAL .x0 (jOff (-(4 * (chainStepA.length + 1))))]

/-- Implementation B: constants hoisted out of the loop, the tweak position
    `8 i + pos` kept directly in `x15`, the bound `8 i + 7` in `x17`. -/
def chainStepB : Program :=
  [.SLLI .x6 .x15 32, .ADDI .x6 .x6 0x100, .SD .x7 .x6 0, .ECALL,
   .LD .x28 .x12 0, .LD .x29 .x12 8, .SD .x7 .x28 32, .SD .x7 .x29 40,
   .ADDI .x15 .x15 1]

def chainWalkB : Program :=
  [.LI .x7 BUFA, .LI .x5 HASH_ID, .LI .x10 BUFA, .LI .x11 48, .LI .x12 OUT,
   .SLLI .x6 .x8 32, .SD .x7 .x6 8, .ADD .x15 .x16 .x14, .ADDI .x17 .x16 7,
   .BGE .x15 .x17 (bOff (4 * (chainStepB.length + 2)))] ++
  chainStepB ++ [.JAL .x0 (jOff (-(4 * (chainStepB.length + 1))))]

/-- The chain-walk implementation the verifier is built with. -/
def chainWalk : Program := chainWalkA

/-- Store `CUR` as endpoint `i`, advance the four loop registers. -/
def chainStore : Program :=
  [.LI .x6 CUR, .LD .x28 .x6 0, .LD .x29 .x6 8, .SD .x18 .x28 0, .SD .x18 .x29 8,
   .ADDI .x13 .x13 1, .ADDI .x18 .x18 16, .ADDI .x19 .x19 8, .ADDI .x16 .x16 8, .LI .x6 42]

def chainsBody : Program := chainLoad ++ chainWalk ++ chainStore

def chainsLoop : Program := chainsBody ++ [.BNE .x13 .x6 (bOff (-(4 * chainsBody.length)))]

def chains : Program := chainsPre ++ chainsLoop

/-! ## leaf -/

def leaf : Program :=
  [.LI .x7 0x200, .LI .x6 BUFL, .SD .x6 .x7 0, .SLLI .x7 .x8 32, .SD .x6 .x7 8,
   .LI .x5 HASH_ID, .LI .x10 BUFL, .LI .x11 704, .LI .x12 OUT, .ECALL,
   .LI .x6 OUT, .LD .x28 .x6 0, .LD .x29 .x6 8, .LI .x6 CUR, .SD .x6 .x28 0, .SD .x6 .x29 8]

/-! ## auth -/

def authPre : Program := [.LI .x25 0, .LI .x26 AUTH]

/-- Load sibling and current node, test bit `L` of the epoch, and lay the two
    children out in the payload in the order the bit dictates. -/
def authSelect : Program :=
  [.LD .x28 .x26 0, .LD .x29 .x26 8, .LI .x6 CUR, .LD .x30 .x6 0, .LD .x31 .x6 8,
   .SRL .x7 .x8 .x25, .ANDI .x7 .x7 1, .BEQ .x7 .x0 (bOff 24),
   .SD .x6 .x28 0, .SD .x6 .x29 8, .SD .x6 .x30 16, .SD .x6 .x31 24, .JAL .x0 (jOff 12),
   .SD .x6 .x28 16, .SD .x6 .x29 24]

/-- Write the merkle tweak, hash, and store the parent into `CUR`. -/
def authHash : Program :=
  [.ADDI .x7 .x25 1, .SLLI .x7 .x7 32, .ADDI .x7 .x7 0x300, .LI .x6 BUFA, .SD .x6 .x7 0,
   .ADDI .x7 .x25 1, .SRL .x7 .x8 .x7, .SLLI .x7 .x7 32, .SD .x6 .x7 8,
   .LI .x5 HASH_ID, .LI .x10 BUFA, .LI .x11 64, .LI .x12 OUT, .ECALL,
   .LI .x6 OUT, .LD .x28 .x6 0, .LD .x29 .x6 8, .LI .x6 CUR, .SD .x6 .x28 0, .SD .x6 .x29 8,
   .ADDI .x25 .x25 1, .ADDI .x26 .x26 16, .LI .x6 32]

def authBody : Program := authSelect ++ authHash

def authLoop : Program := authBody ++ [.BNE .x25 .x6 (bOff (-(4 * authBody.length)))]

def auth : Program := authPre ++ authLoop

/-! ## final -/

def final : Program :=
  [.LI .x6 CUR, .LD .x28 .x6 0, .LD .x29 .x6 8, .LI .x6 ROOT, .LD .x30 .x6 0, .LD .x31 .x6 8,
   .BNE .x28 .x30 (bOff 20), .BNE .x29 .x31 (bOff 16)] ++ haltWith 1 ++ haltWith 0

/-! ## The verifier -/

def verifier : Program := init ++ decode ++ chains ++ leaf ++ auth ++ final

/-- The code map the correctness theorem assumes: `verifier` loaded at
    `CODE_BASE`, nothing else. -/
def verifierCode : CodeMem := loadProgram CODE_BASE verifier

/-- Address of instruction index `k`. -/
def addr (k : Nat) : Word := CODE_BASE + BitVec.ofNat 64 (4 * k)

/-! ## Region boundaries, as instruction indices -/

def idxInitPayload : Nat := initP.length
def idxInitHash : Nat := idxInitPayload + initPayload.length
def idxDecode : Nat := init.length
def idxDecodeLoop : Nat := idxDecode + decodePre.length
def idxDecodePost : Nat := idxDecodeLoop + decodeLoop.length
def idxDecodeReject : Nat := idxDecodePost + 3
def idxChains : Nat := idxDecode + decode.length
def idxChainsLoop : Nat := idxChains + chainsPre.length
def idxChainWalk : Nat := idxChainsLoop + chainLoad.length
def idxChainStore : Nat := idxChainWalk + chainWalk.length
def idxLeaf : Nat := idxChains + chains.length
def idxAuth : Nat := idxLeaf + leaf.length
def idxAuthLoop : Nat := idxAuth + authPre.length
def idxAuthHash : Nat := idxAuthLoop + authSelect.length
def idxFinal : Nat := idxAuth + auth.length
def idxAccept : Nat := idxFinal + 8
def idxReject : Nat := idxAccept + 3
def idxEnd : Nat := verifier.length

/-- Static instruction count. -/
example : verifier.length = idxEnd := rfl

end XmssAsm

namespace XmssAsm

/-! ## Index values, for the simp set -/

theorem idxInitPayload_eq : idxInitPayload = 9 := by decide +kernel
theorem idxInitHash_eq : idxInitHash = 28 := by decide +kernel
theorem idxDecode_eq : idxDecode = 43 := by decide +kernel
theorem idxDecodeLoop_eq : idxDecodeLoop = 52 := by decide +kernel
theorem idxDecodePost_eq : idxDecodePost = 62 := by decide +kernel
theorem idxDecodeReject_eq : idxDecodeReject = 65 := by decide +kernel
theorem idxChains_eq : idxChains = 68 := by decide +kernel
theorem idxChainsLoop_eq : idxChainsLoop = 72 := by decide +kernel
theorem idxChainWalk_eq : idxChainWalk = 81 := by decide +kernel
theorem idxChainStore_eq : idxChainStore = 103 := by decide +kernel
theorem idxLeaf_eq : idxLeaf = 114 := by decide +kernel
theorem idxAuth_eq : idxAuth = 130 := by decide +kernel
theorem idxAuthLoop_eq : idxAuthLoop = 132 := by decide +kernel
theorem idxAuthHash_eq : idxAuthHash = 147 := by decide +kernel
theorem idxFinal_eq : idxFinal = 171 := by decide +kernel
theorem idxAccept_eq : idxAccept = 179 := by decide +kernel
theorem idxReject_eq : idxReject = 182 := by decide +kernel
theorem idxEnd_eq : idxEnd = 185 := by decide +kernel

end XmssAsm
