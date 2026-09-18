/-
  XmssAsmTests.Cycles -- `lake exe cycles`

  Region-by-region virtual-cycle counts on accepting fixtures. The OTS
  subtotal is init + decode + 42 WOTS chains + leaf (the recovered OTS
  public key). The Merkle authentication path is reported separately.
-/

import XmssAsmTests

open XmssAsm XmssAsm.Tests RiscvZkvm.Rv64 XmssSecurity

/-- Steps/hashes to get from `s` to the instruction at index `idx`. -/
def leg (s : MachineState) (idx : Nat) : MachineState × Nat × Nat × Bool :=
  let (s', st, ok) := runUntil H_test 100000 s (addr idx) {}
  (s', st.steps, st.hashes, ok)

def report (f : Fixture) : IO Unit := do
  let s0 := initState f.pk f.ep f.msg f.sig
  let (s1, i1, h1, k1) := leg s0 idxDecode
  let (s2, i2, h2, k2) := leg s1 idxChains
  let (s3, i3, h3, k3) := leg s2 idxLeaf
  let (s4, i4, h4, k4) := leg s3 idxAuth
  let (s5, i5, h5, k5) := leg s4 idxFinal
  let (_, st6, stop) := runH H_test verifierFuel s5 {}
  let ok := k1 && k2 && k3 && k4 && k5 && (stop == Stop.halted)
  let ots := i1 + i2 + i3 + i4
  let otsH := h1 + h2 + h3 + h4
  let tot := ots + i5 + st6.steps
  let totH := otsH + h5 + st6.hashes
  let r := runFixture f
  IO.println s!"{f.name} boundaries-ok={ok} halted={r.halted} a0={r.a0.toNat}"
  IO.println s!"  init(encoding hash) {i1} steps {h1} hash"
  IO.println s!"  decode digits       {i2} steps {h2} hash"
  IO.println s!"  42 WOTS chains      {i3} steps {h3} hash"
  IO.println s!"  leaf (OTS pubkey)   {i4} steps {h4} hash"
  IO.println s!"  == OTS subtotal     {ots} steps {otsH} hash   cost@1={ots}"
  IO.println s!"  auth path (tree)    {i5} steps {h5} hash"
  IO.println s!"  final compare       {st6.steps} steps {st6.hashes} hash"
  IO.println s!"  == TOTAL            {tot} steps {totH} hash   cost@1={tot}"

def main : IO UInt32 := do
  IO.println "== xmss-asm OTS / XMSS virtual-cycle breakdown =="
  IO.println "cost model: 1 executed RV instruction = 1 virtual cycle; hash ECALL counts as 1 step"
  IO.println "OTS = init + decode + 42 WOTS chains + leaf; Merkle path excluded"
  let mut n := 0
  for f in corpus do
    if f.expected then
      n := n + 1
      report f
  IO.println s!"{n} accepting fixtures"
  return 0
