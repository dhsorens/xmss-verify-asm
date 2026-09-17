/-
  XmssAsmTests.TestHash

  `H_test`: a deterministic, executable, non-cryptographic hash used to make
  both the specification and the machine executable on the same oracle.
-/

import XmssSecurity.Scheme

namespace XmssAsm.Tests

open XmssSecurity

/-- A 64-bit mixing step (FNV-1a style multiply-xor). -/
def mix (acc : UInt64) (b : UInt8) : UInt64 := (acc ^^^ b.toUInt64) * 0x100000001b3

/-- splitmix64's finalizer. -/
def fin64 (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

/-- The test oracle: fold the bytes, then derive four output words. -/
def H_test (input : HashInput) : HashOutput :=
  let h := input.foldl mix (0xcbf29ce484222325 + input.length.toUInt64)
  let w0 := fin64 (h + 0x9E3779B97F4A7C15)
  let w1 := fin64 (h + 0x3C6EF372FE94F82A)
  let w2 := fin64 (h + 0xDAA66D2C7DDF143F)
  let w3 := fin64 (h + 0x78DDE6E5FD29A054)
  w3.toBitVec ++ w2.toBitVec ++ w1.toBitVec ++ w0.toBitVec

end XmssAsm.Tests
