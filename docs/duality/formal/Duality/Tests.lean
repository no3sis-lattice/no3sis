/-
Test suite entry point for Duality library
Imports all test modules
-/

import Duality.Tests.BaseTests
import Duality.Tests.ChunkConsistency
import Duality.Tests.Regression
import Duality.Tests.TranspilerCorrectness

namespace Duality.Tests

/-- Test suite version -/
def version : String := "1.1.0"

/-- Test suite description -/
def description : String :=
  "Test suite for TRUE_DUAL_TRACT formalization. " ++
  "Includes property tests, integration tests, regression tests, " ++
  "and transpiler correctness proofs (Phase 9a)."

end Duality.Tests
