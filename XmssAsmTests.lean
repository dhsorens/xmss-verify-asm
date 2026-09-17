/-
  XmssAsmTests

  The executable checks (PLAN E2/E3): a deterministic test hash, fixture
  generation from the specification's own algorithms, component-level and
  end-to-end differential tests, and the cycle report. Not part of the trust
  base; nothing here is imported by a theorem.
-/

import XmssAsmTests.TestHash
import XmssAsmTests.Fixtures
import XmssAsmTests.Diff
