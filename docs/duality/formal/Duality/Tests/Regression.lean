/-
Regression tests for build system stability
Prevents breakage during refactoring
-/

import Duality.Base
import Duality.Chunks.Chunk01
import Duality.Chunks.Chunk62

namespace Duality.Tests

open Duality

/-- Regression: N value must not change -/
example : N = 100 := rfl

/-- Regression: X8 has exactly 8 fields -/
example (x : X8) : x = ⟨x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8⟩ := by
  cases x
  rfl

/-- Regression: standardWitness has expected structure -/
example : standardWitness = ⟨100, 0, 0, 0, 0, 0, 0, 0⟩ := rfl

/-- Regression: unitary definition unchanged -/
example (x : X8) :
  unitary x = (x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N) := rfl

/-- Regression: standardWitness_unitary theorem still available -/
example : unitary standardWitness := standardWitness_unitary

/-- Regression: Chunk01 namespace exists and has required definitions -/
example : ∃ x : X8, unitary x ∧ Chunk01.domainConstraints := Chunk01.exists_solution

/-- Regression: Chunk62 namespace exists and has required definitions -/
example : ∃ x : X8, unitary x ∧ Chunk62.domainConstraints := Chunk62.exists_solution

/-- Regression: All chunks should prove with trivial constraints -/
example : Chunk01.domainConstraints := trivial
example : Chunk62.domainConstraints := trivial

/-- Regression: Proof pattern still works -/
theorem regression_proof_pattern : ∃ x : X8, unitary x ∧ True := by
  refine ⟨standardWitness, ?_, ?_⟩
  · exact standardWitness_unitary
  · trivial

end Duality.Tests
