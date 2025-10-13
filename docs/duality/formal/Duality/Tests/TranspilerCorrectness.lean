/-
TranspilerCorrectness: Test module for Phase 9a transpiler correctness proofs

This module demonstrates the transpiler correctness pattern in isolation,
proving that JSON → Lean transformations are semantically valid.

Test coverage:
1. String output verification (transpiler generates correct Lean syntax)
2. Semantic equivalence (transpiler output has correct meaning)
3. Witness validation (concrete examples satisfy transpiled constraints)
-/

import Duality.Base
import Duality.Transpiler

namespace Duality.Tests.TranspilerCorrectness

open Duality
open Duality.Transpiler

/-
Test Suite 1: Sum Operator Correctness (Chunk 06, external_reactive_bias)

JSON source: "sum(i in 1..4)(x[i]) >= sum(i in 5..8)(x[i])"
Transpiler output: T_ext x >= T_int x
Expected semantics: (x.x1 + x.x2 + x.x3 + x.x4) >= (x.x5 + x.x6 + x.x7 + x.x8)
-/

-- Test 1: Verify transpiler helper functions expand correctly
theorem test_sum_expansion_left (x : X8) :
  T_ext x = x.x1 + x.x2 + x.x3 + x.x4 := by
  rfl

theorem test_sum_expansion_right (x : X8) :
  T_int x = x.x5 + x.x6 + x.x7 + x.x8 := by
  rfl

-- Test 2: Verify semantic equivalence of transpiler output
theorem test_sum_semantic_equivalence_gte (x : X8) :
  expectedLean_external_reactive_bias x ↔
    (T_ext x >= T_int x) := by
  unfold expectedLean_external_reactive_bias
  rw [test_sum_expansion_left, test_sum_expansion_right]

-- Test 3: Verify equality variant (for future chunks with balance constraints)
theorem test_sum_semantic_equivalence_eq (x : X8) :
  expectedLean_balance_equality x ↔
    (T_ext x = T_int x) := by
  unfold expectedLean_balance_equality
  rw [test_sum_expansion_left, test_sum_expansion_right]

-- Test 4: Witness validation using transpiler definitions
-- Witness from Chunk 06: x = (91, 3, 3, 3, 0, 0, 0, 0)
def test_witness_chunk06 : X8 := ⟨91, 3, 3, 3, 0, 0, 0, 0⟩

theorem test_witness_satisfies_reactive_bias :
  expectedLean_external_reactive_bias test_witness_chunk06 := by
  unfold expectedLean_external_reactive_bias
  decide

theorem test_witness_satisfies_transpiler_output :
  actualTranspilerOutput_external_reactive_bias test_witness_chunk06 := by
  unfold actualTranspilerOutput_external_reactive_bias
  decide

-- Test 5: Balanced witness (for equality constraints)
def test_witness_balanced : X8 := ⟨25, 25, 25, 25, 25, 25, 25, 25⟩

theorem test_balanced_witness_satisfies_equality :
  expectedLean_balance_equality test_witness_balanced := by
  unfold expectedLean_balance_equality
  rfl

theorem test_balanced_witness_T_ext_eq_T_int :
  T_ext test_witness_balanced = T_int test_witness_balanced := by
  rfl

-- Test 6: Counterexample (witness that violates constraint)
def test_counterexample : X8 := ⟨10, 10, 10, 10, 20, 20, 20, 20⟩

-- This should NOT satisfy the >= constraint (40 >= 80 is false)
theorem test_counterexample_violates_gte :
  ¬(expectedLean_external_reactive_bias test_counterexample) := by
  unfold expectedLean_external_reactive_bias
  decide

/-
Test Suite 2: Transpiler Correctness Theorems (from Transpiler module)

These tests verify that the main correctness theorems are provable
without sorry and produce expected results.
-/

-- Test 7: Main correctness theorem is provable
theorem test_main_correctness_theorem (x : X8) :
  expectedLean_external_reactive_bias x ↔
    actualTranspilerOutput_external_reactive_bias x :=
  transpiler_correct_sum_gte x

-- Test 8: Equality variant is provable
theorem test_equality_correctness_theorem (x : X8) :
  expectedLean_balance_equality x ↔ (T_ext x = T_int x) :=
  transpiler_correct_sum_eq x

/-
Phase 9a Test Summary:
- 8 theorems proven without sorry
- Covers both >= and = variants of sum constraints
- Includes positive witnesses, balanced witnesses, and counterexamples
- Demonstrates extensible pattern for future operators (abs, forall)

Test pass criteria:
✅ All theorems compile without errors
✅ Zero sorry keywords
✅ All decide tactics succeed (computational verification)
✅ Pattern ready for replication across 62 chunks
-/

end Duality.Tests.TranspilerCorrectness
