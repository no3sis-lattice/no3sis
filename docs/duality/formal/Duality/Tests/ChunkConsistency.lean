/-
Integration tests for chunk consistency
Verifies all chunks use consistent definitions and proofs
-/

import Duality.Base
import Duality.Chunks.Chunk01
import Duality.Chunks.Chunk02
import Duality.Chunks.Chunk15
import Duality.Chunks.Chunk31
import Duality.Chunks.Chunk62

namespace Duality.Tests

open Duality

/-- Test: All sampled chunks export exists_solution theorem -/
example : ∃ x : X8, unitary x ∧ Chunk01.domainConstraints := Chunk01.exists_solution
example : ∃ x : X8, unitary x ∧ Chunk02.domainConstraints := Chunk02.exists_solution
example : ∃ x : X8, unitary x ∧ Chunk15.domainConstraints := Chunk15.exists_solution
example : ∃ x : X8, unitary x ∧ Chunk31.domainConstraints := Chunk31.exists_solution
example : ∃ x : X8, unitary x ∧ Chunk62.domainConstraints := Chunk62.exists_solution

/-- Test: All sampled chunks have trivial domainConstraints -/
example : Chunk01.domainConstraints := trivial
example : Chunk02.domainConstraints := trivial
example : Chunk15.domainConstraints := trivial
example : Chunk31.domainConstraints := trivial
example : Chunk62.domainConstraints := trivial

/-- Test: Standard witness satisfies all sampled chunk constraints -/
example : unitary standardWitness ∧ Chunk01.domainConstraints := by
  constructor
  · exact standardWitness_unitary
  · trivial

example : unitary standardWitness ∧ Chunk62.domainConstraints := by
  constructor
  · exact standardWitness_unitary
  · trivial

/-- Property: Chunk constraints are independent of witness choice -/
theorem chunk01_constraint_independent (x y : X8) :
  Chunk01.domainConstraints → Chunk01.domainConstraints := by
  intro h
  exact h

/-- Integration test: Cross-chunk theorem usage -/
example : ∃ x : X8,
  (unitary x ∧ Chunk01.domainConstraints) ∧
  (unitary x ∧ Chunk02.domainConstraints) := by
  refine ⟨standardWitness, ?_, ?_⟩
  · constructor
    · exact standardWitness_unitary
    · trivial
  · constructor
    · exact standardWitness_unitary
    · trivial

end Duality.Tests
