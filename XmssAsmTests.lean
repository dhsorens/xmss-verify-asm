/-
  XmssAsmTests

  The executable checks: a deterministic test hash, fixture generation from
  the specification's own algorithms, component-level and end-to-end
  differential tests, and the cycle report. Not part of the trust base;
  nothing here is imported by a theorem, and none of it is a merge gate.
-/

import XmssAsmTests.TestHash
import XmssAsmTests.Fixtures
import XmssAsmTests.Diff
import XmssAsmTests.Regions
import XmssAsmTests.Cost
import XmssAsmTests.Rejects
