/-
Phase 6b: Pilot Equivalence Tests
Verifies that pilot chunks (06, 09, 19) properly transpile JSON constraints to Lean.

Tests:
1. All transpiler artifacts (sum, forall, abs) are resolved
2. Helper functions (bridgeBalance, uniformityConstraint) are used correctly
3. Witness proofs still work
4. Equivalence lemmas compile and prove correctly
-/

import Duality.Base
import Duality.Lemmas
import Duality.Chunks.Chunk06
import Duality.Chunks.Chunk09
import Duality.Chunks.Chunk19

namespace Duality.Tests.PilotEquivalence

open Duality

-- Test 1: Verify no 'sum' artifacts remain in generated constraints
-- The transpiler should have expanded sum(i in 1..N)(x[i]) to explicit additions
-- or used helper functions like T_ext, T_int

theorem chunk06_uses_explicit_sums :
  ∀ x : X8,
    Chunk06.domainConstraints x →
    (x.x1 + x.x2 + x.x3 >= 30)  -- external_min_viable uses explicit sum
    := by
  intro x h
  unfold Chunk06.domainConstraints at h
  exact h.2.2.1

theorem chunk06_sum_comparison_works :
  ∀ x : X8,
    Chunk06.domainConstraints x →
    -- external_reactive_bias: sum(1..4) >= sum(5..8) expanded to explicit comparison
    (x.x1 + x.x2 + x.x3 + x.x4 >= x.x5 + x.x6 + x.x7 + x.x8)
    := by
  intro x h
  unfold Chunk06.domainConstraints at h
  exact h.2.2.2.1

-- Test 2: Verify 'abs' is resolved to bridgeBalance helper

theorem chunk09_uses_bridgeBalance :
  ∀ x : X8,
    Chunk09.domainConstraints x →
    bridgeBalance x.x1 x.x2 5  -- abs(x[1] - x[2]) <= 5 → bridgeBalance
    := by
  intro x h
  unfold Chunk09.domainConstraints at h
  exact h.2.2.2.1

theorem chunk19_uses_pairwise_bridgeBalance :
  ∀ x : X8,
    Chunk19.domainConstraints x →
    bridgeBalance x.x1 x.x2 20  -- First of 28 pairwise constraints
    := by
  intro x h
  unfold Chunk19.domainConstraints at h
  exact h.2.2.2.1.1

-- Test 3: Verify 'forall' is resolved to explicit conjunctions or helper functions

theorem chunk06_forall_expanded :
  ∀ x : X8,
    Chunk06.domainConstraints x →
    (x.x1 >= 3 ∧ x.x2 >= 3 ∧ x.x3 >= 3 ∧ x.x4 >= 3)  -- forall(i in 1..4)(x[i] >= 3) expanded
    := by
  intro x h
  unfold Chunk06.domainConstraints at h
  exact h.2.2.2.2

theorem chunk19_uses_uniformityConstraint :
  ∀ x : X8,
    Chunk19.domainConstraints x →
    uniformityConstraint x 1 8 5  -- forall(i in 1..8)(x[i] >= 5) → helper
    := by
  intro x h
  unfold Chunk19.domainConstraints at h
  exact h.2.2.1

-- Test 4: Verify witness proofs still work (regression test)

theorem chunk06_witness_works :
  unitary Chunk06.witness ∧ Chunk06.domainConstraints Chunk06.witness := by
  exact Chunk06.witness_valid

theorem chunk09_witness_works :
  unitary Chunk09.witness ∧ Chunk09.domainConstraints Chunk09.witness := by
  exact Chunk09.witness_valid

theorem chunk19_witness_works :
  unitary Chunk19.witness ∧ Chunk19.domainConstraints Chunk19.witness := by
  exact Chunk19.witness_valid

-- Test 5: Verify equivalence lemmas compile

theorem chunk06_equivalence_compiles :
  ∀ x : X8, Chunk06.domainConstraints x ↔
    (True ∧ True ∧ (x.x1 + x.x2 + x.x3 >= 30) ∧ (T_ext x >= T_int x) ∧
     (x.x1 >= 3 ∧ x.x2 >= 3 ∧ x.x3 >= 3 ∧ x.x4 >= 3)) := by
  intro x
  exact Chunk06.jsonSpec_equiv_domain x

theorem chunk09_equivalence_compiles :
  ∀ x : X8, Chunk09.domainConstraints x ↔
    (True ∧ True ∧ (x.x1 + x.x2 >= 10) ∧ (bridgeBalance x.x1 x.x2 5) ∧
     (x.x1 + x.x2 + x.x3 <= 40)) := by
  intro x
  exact Chunk09.jsonSpec_equiv_domain x

theorem chunk19_equivalence_compiles :
  ∀ x : X8, Chunk19.domainConstraints x ↔
    (True ∧ True ∧ (uniformityConstraint x 1 8 5) ∧
     ((bridgeBalance x.x1 x.x2 20) ∧ (bridgeBalance x.x1 x.x3 20) ∧ (bridgeBalance x.x1 x.x4 20) ∧
      (bridgeBalance x.x1 x.x5 20) ∧ (bridgeBalance x.x1 x.x6 20) ∧ (bridgeBalance x.x1 x.x7 20) ∧
      (bridgeBalance x.x1 x.x8 20) ∧ (bridgeBalance x.x2 x.x3 20) ∧ (bridgeBalance x.x2 x.x4 20) ∧
      (bridgeBalance x.x2 x.x5 20) ∧ (bridgeBalance x.x2 x.x6 20) ∧ (bridgeBalance x.x2 x.x7 20) ∧
      (bridgeBalance x.x2 x.x8 20) ∧ (bridgeBalance x.x3 x.x4 20) ∧ (bridgeBalance x.x3 x.x5 20) ∧
      (bridgeBalance x.x3 x.x6 20) ∧ (bridgeBalance x.x3 x.x7 20) ∧ (bridgeBalance x.x3 x.x8 20) ∧
      (bridgeBalance x.x4 x.x5 20) ∧ (bridgeBalance x.x4 x.x6 20) ∧ (bridgeBalance x.x4 x.x7 20) ∧
      (bridgeBalance x.x4 x.x8 20) ∧ (bridgeBalance x.x5 x.x6 20) ∧ (bridgeBalance x.x5 x.x7 20) ∧
      (bridgeBalance x.x5 x.x8 20) ∧ (bridgeBalance x.x6 x.x7 20) ∧ (bridgeBalance x.x6 x.x8 20) ∧
      (bridgeBalance x.x7 x.x8 20)) ∧
     (primeAlignment x.x1 2 ∧ primeAlignment x.x2 3)) := by
  intro x
  exact Chunk19.jsonSpec_equiv_domain x

-- Summary: All tests verify that transpiler correctly:
-- 1. Expands sum() to explicit additions or tract helpers
-- 2. Converts abs() to bridgeBalance helper
-- 3. Expands forall() to conjunctions or uniformityConstraint helper
-- 4. Preserves witness proofs across changes
-- 5. Generates provable equivalence lemmas

end Duality.Tests.PilotEquivalence
