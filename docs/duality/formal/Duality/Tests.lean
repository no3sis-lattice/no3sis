/-
Test suite entry point for Duality library
Imports all test modules
-/

import Duality.Tests.BaseTests
import Duality.Tests.ChunkConsistency
import Duality.Tests.Regression

namespace Duality.Tests

/-- Test suite version -/
def version : String := "1.0.0"

/-- Test suite description -/
def description : String :=
  "Test suite for TRUE_DUAL_TRACT formalization. " ++
  "Includes property tests, integration tests, and regression tests."

end Duality.Tests
