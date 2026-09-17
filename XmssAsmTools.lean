/-
  XmssAsmTools

  Build-time tooling. Not part of the verification: nothing under
  `XmssAsmTools` is imported by a theorem. It is in `defaultTargets` so that a
  syntax error in the gate fails the ordinary build.
-/

module

public import XmssAsmTools.AxiomSweep
