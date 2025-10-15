#!/usr/bin/env python3
"""
Unit tests for Phase 3 transpiler scripts.
Tests TDD principles: operator mappings, edge cases, and regression tests.
Phase 6b: Extended with additional complexity tests

Usage:
  pytest test_transpilers.py -v
  python3 -m pytest test_transpilers.py --cov=. --cov-report=term-missing
"""

import json
import pytest
import random
import subprocess
import tempfile
from pathlib import Path
from typing import Dict

# Import functions to test
from transpile_to_mzn import (
    translate_expr_to_mzn,
    generate_mzn_from_json,
    OPERATOR_MAP as MZN_OPERATOR_MAP,
)
# Note: discover_chunks removed (Phase 5 - not in transpile_to_mzn anymore)
from transpile_to_lean import (
    translate_expr_to_lean,
    generate_lean_from_json,
    OPERATOR_MAP as LEAN_OPERATOR_MAP,
)
from add_constraints import (
    detect_chunk_type,
    count_existing_constraints,
    generate_constraint_from_template,
    add_constraints_to_chunk,
)


# ============================================================================
# Tests for transpile_to_mzn.py
# ============================================================================

class TestTranspileToMzn:
    """Test suite for JSON → MiniZinc transpiler."""

    def test_operator_and_translation(self):
        """Test && → /\\ translation."""
        expr = "x[1] > 5 && x[2] < 10"
        result = translate_expr_to_mzn(expr)
        assert "/\\" in result
        assert "&&" not in result

    def test_operator_or_translation(self):
        """Test || → \\/ translation."""
        expr = "x[1] = 5 || x[2] = 10"
        result = translate_expr_to_mzn(expr)
        assert "\\/" in result
        assert "||" not in result

    def test_operator_not_translation(self):
        """Test ! → not translation."""
        expr = "!(x[1] > 5)"
        result = translate_expr_to_mzn(expr)
        assert "not" in result
        assert "!" not in result

    def test_operator_modulo_translation(self):
        """Test % → mod translation."""
        expr = "x[1] % 3 = 0"
        result = translate_expr_to_mzn(expr)
        assert "mod" in result
        assert "%" not in result

    def test_operator_equality_translation(self):
        """Test == → = translation (but != stays)."""
        expr = "x[1] == 5 && x[2] != 3"
        result = translate_expr_to_mzn(expr)
        assert "x[1] = 5" in result or "x[1]= 5" in result or "x[1] =5" in result
        assert "!=" in result  # Should preserve

    def test_sum_stays_unchanged(self):
        """Test sum(i in 1..4)(x[i]) stays as-is."""
        expr = "sum(i in 1..4)(x[i]) >= 10"
        result = translate_expr_to_mzn(expr)
        assert "sum(i in 1..4)(x[i])" in result

    def test_forall_stays_unchanged(self):
        """Test forall(i in 1..4)(...) stays as-is."""
        expr = "forall(i in 1..4)(x[i] >= 3)"
        result = translate_expr_to_mzn(expr)
        assert "forall(i in 1..4)(x[i] >= 3)" in result

    def test_count_converts_to_sum(self):
        """Test count(i in S)(P) → sum(i in S)(P) with implicit bool2int."""
        expr = "count(i in 1..8)(x[i] > 0) >= 3"
        result = translate_expr_to_mzn(expr)
        assert "sum(i in 1..8)(x[i] > 0) >= 3" in result
        assert "count" not in result

    def test_true_false_literals(self):
        """Test true/false case normalization."""
        expr1 = "True && False"
        expr2 = "TRUE || FALSE"
        result1 = translate_expr_to_mzn(expr1)
        result2 = translate_expr_to_mzn(expr2)
        assert "true" in result1.lower()
        assert "false" in result1.lower()
        assert "true" in result2.lower()
        assert "false" in result2.lower()

    def test_complex_expression(self):
        """Test multiple operators in one expression."""
        expr = "x[1] % 2 = 0 && (x[2] == 3 || x[3] != 5) && !x[4] > 10"
        result = translate_expr_to_mzn(expr)
        assert "mod" in result
        assert "/\\" in result
        assert "\\/" in result
        assert "not" in result

    def test_array_indexing_preserved(self):
        """Test x[i] indexing is preserved for MiniZinc."""
        expr = "x[1] + x[2] = x[3]"
        result = translate_expr_to_mzn(expr)
        assert "x[1]" in result
        assert "x[2]" in result
        assert "x[3]" in result

    def test_generate_mzn_from_json(self):
        """Test full JSON → MiniZinc generation."""
        json_data = {
            "id": "06",
            "title": "Test Chunk",
            "parameters": {
                "scaleN": 100,
                "monsterPrimes": [2, 3, 5, 7]
            },
            "constraints": [
                {"name": "test_constraint", "expr": "x[1] >= 10 && x[2] <= 20"}
            ]
        }
        result = generate_mzn_from_json(json_data)

        # Check header
        assert "int: N = 100" in result
        assert "set of int: P = { 2, 3, 5, 7 }" in result

        # Check constraint translated
        assert "/\\" in result
        assert "constraint" in result


# ============================================================================
# Tests for transpile_to_lean.py
# ============================================================================

class TestTranspileToLean:
    """Test suite for JSON → Lean4 transpiler."""

    def test_operator_and_translation(self):
        """Test && → ∧ translation."""
        expr = "x[1] > 5 && x[2] < 10"
        result = translate_expr_to_lean(expr)
        assert "∧" in result
        assert "&&" not in result

    def test_operator_or_translation(self):
        """Test || → ∨ translation."""
        expr = "x[1] = 5 || x[2] = 10"
        result = translate_expr_to_lean(expr)
        assert "∨" in result
        assert "||" not in result

    def test_operator_not_translation(self):
        """Test ! → ¬ translation."""
        expr = "!(x[1] > 5)"
        result = translate_expr_to_lean(expr)
        assert "¬" in result
        assert "!" not in result

    def test_operator_implies_translation(self):
        """Test -> → → translation."""
        expr = "x[1] > 5 -> x[2] > 10"
        result = translate_expr_to_lean(expr)
        assert "→" in result

    def test_operator_inequality_translation(self):
        """Test != → ≠ translation."""
        expr = "x[1] != 5"
        result = translate_expr_to_lean(expr)
        assert "≠" in result
        assert "!=" not in result

    def test_array_indexing_translation(self):
        """Test x[1] → x.x1, x[2] → x.x2 translation."""
        expr = "x[1] + x[2] = x[3]"
        result = translate_expr_to_lean(expr)
        assert "x.x1" in result
        assert "x.x2" in result
        assert "x.x3" in result
        assert "x[" not in result

    def test_sum_expansion(self):
        """Test sum(i in 1..4)(x[i]) → x.x1 + x.x2 + x.x3 + x.x4."""
        expr = "sum(i in 1..4)(x[i]) >= 10"
        result = translate_expr_to_lean(expr)
        assert "x.x1 + x.x2 + x.x3 + x.x4" in result
        assert "sum" not in result

    def test_sum_expansion_atomic_regression(self):
        """
        REGRESSION TEST for Blocker 1: Sum Expansion Double-Substitution.

        Test that multiple sum() expressions in same line don't corrupt each other.
        This was discovered as a bug during Phase 3 execution.
        """
        expr = "sum(i in 1..4)(x[i]) >= sum(i in 5..8)(x[i])"
        result = translate_expr_to_lean(expr)

        # Should have both sides expanded correctly
        assert "x.x1 + x.x2 + x.x3 + x.x4" in result
        assert "x.x5 + x.x6 + x.x7 + x.x8" in result

        # Should NOT have double-expansion artifacts
        assert result.count("x.x5") == 1
        assert result.count("x.x1") == 1

    def test_forall_expansion(self):
        """Test forall(i in 1..3)(x[i] >= 5) → x.x1 >= 5 ∧ x.x2 >= 5 ∧ x.x3 >= 5."""
        expr = "forall(i in 1..3)(x[i] >= 5)"
        result = translate_expr_to_lean(expr)
        assert "x.x1 >= 5" in result
        assert "x.x2 >= 5" in result
        assert "x.x3 >= 5" in result
        assert "∧" in result
        assert "forall" not in result

    def test_forall_two_var_expansion(self):
        """
        PHASE 5.5: Test forall(i, j in 1..3 where i < j)(expr) expansion.

        Should expand to conjunction of all valid (i,j) pairs where i < j.
        """
        expr = "forall(i, j in 1..3 where i < j)(x[i] + x[j] >= 10)"
        result = translate_expr_to_lean(expr)

        # Should have pairs: (1,2), (1,3), (2,3)
        assert "x.x1 + x.x2 >= 10" in result
        assert "x.x1 + x.x3 >= 10" in result
        assert "x.x2 + x.x3 >= 10" in result

        # Should be connected with ∧
        assert "∧" in result

        # Should NOT have forall left over
        assert "forall" not in result

    def test_forall_two_var_with_abs(self):
        """
        PHASE 5.5: Test forall with abs pattern from Chunk 19.

        Pattern: forall(i, j in 1..8 where i < j)(abs(x[i] - x[j]) <= 20)
        """
        expr = "forall(i, j in 1..2 where i < j)(abs(x[i] - x[j]) <= 10)"
        result = translate_expr_to_lean(expr)

        # Should expand the forall to single pair (1,2)
        # Should expand abs to Int casts
        assert "x.x1" in result
        assert "x.x2" in result
        assert "Int" in result
        assert "∧" in result  # From abs expansion

        # Should NOT have forall or abs left over
        assert "forall" not in result
        assert "abs" not in result

    def test_minizinc_boolean_operators(self):
        """
        PHASE 5.5: Test MiniZinc boolean operators /\\ and \\/ translation.

        These appear in raw MiniZinc constraints that need conversion.
        """
        expr1 = "x[1] mod 2 = 0 /\\ x[2] mod 3 = 0"
        result1 = translate_expr_to_lean(expr1)
        assert "∧" in result1
        assert "/\\" not in result1

        expr2 = "x[1] > 10 \\/ x[2] > 20"
        result2 = translate_expr_to_lean(expr2)
        assert "∨" in result2
        assert "\\/" not in result2

    def test_abs_expansion(self):
        """Test abs(x[i] - x[j]) <= k → Int casting and bidirectional constraint."""
        expr = "abs(x[1] - x[2]) <= 5"
        result = translate_expr_to_lean(expr)
        # Should expand to: (x.x1 : Int) - x.x2 ≤ 5 ∧ (x.x2 : Int) - x.x1 ≤ 5
        assert "(x.x1 : Int)" in result or "((x.x1) : Int)" in result
        assert "x.x2" in result
        assert "∧" in result
        assert "abs" not in result

    def test_count_expansion(self):
        """Test count(i in 1..3)(x[i] > 0) → List.sum with boolean mapping."""
        expr = "count(i in 1..3)(x[i] > 0) >= 2"
        result = translate_expr_to_lean(expr)
        assert "List.sum" in result
        assert "List.map" in result
        assert "if" in result and "then 1 else 0" in result
        assert "count" not in result

    def test_int_casting_for_subtraction(self):
        """Test that subtraction gets Int casts to avoid Nat underflow."""
        expr = "x[1] - x[2] >= 0"
        result = translate_expr_to_lean(expr)
        # After array index translation and subtraction handling
        assert "(x.x1 : Int)" in result or "((x.x1) : Int)" in result

    def test_true_false_literals(self):
        """Test true → True, false → False (Lean capitalization)."""
        expr = "true && false"
        result = translate_expr_to_lean(expr)
        assert "True" in result
        assert "False" in result

    def test_complex_nested_expression(self):
        """Test complex expression with multiple transformations."""
        expr = "(x[1] >= 5 && x[2] <= 10) || sum(i in 3..5)(x[i]) > 20"
        result = translate_expr_to_lean(expr)
        assert "x.x1" in result
        assert "x.x2" in result
        assert "x.x3 + x.x4 + x.x5" in result
        assert "∧" in result
        assert "∨" in result

    # PHASE 6b: New test cases

    def test_forall_two_var_with_complex_body(self):
        """
        PHASE 6b: Test forall(i,j) with nested boolean operations in body.

        Verifies correct expansion when body contains compound expressions.
        """
        expr = "forall(i, j in 1..2 where i < j)((x[i] >= 5 && x[j] <= 20) || x[i] + x[j] >= 15)"
        result = translate_expr_to_lean(expr)

        # Should expand forall to single pair (1,2)
        assert "x.x1" in result
        assert "x.x2" in result

        # Body should be present with proper operators
        assert "∧" in result  # From &&
        assert "∨" in result  # From ||

        # Compound operations preserved
        assert ">= 5" in result
        assert "<= 20" in result
        assert ">= 15" in result

        # No forall left over
        assert "forall" not in result

    def test_abs_with_int_cast_in_complex_expr(self):
        """
        PHASE 6b: Test abs() within larger expression with multiple operators.

        Verifies Int casting works correctly when abs is part of compound constraint.
        """
        expr = "x[1] >= 10 && abs(x[1] - x[2]) <= 5 && x[3] <= 50"
        result = translate_expr_to_lean(expr)

        # abs should be expanded with Int casts
        assert "Int" in result
        assert "abs" not in result

        # All three parts of conjunction present
        assert "x.x1 >= 10" in result
        assert "x.x3 <= 50" in result

        # Bidirectional constraint from abs
        assert result.count("∧") >= 3  # At least 3 conjunctions (x1>=10 ∧ abs_part1 ∧ abs_part2 ∧ x3<=50)

    def test_count_with_complex_predicate(self):
        """
        PHASE 6b: Test count() with compound boolean conditions.

        Verifies count expansion handles nested boolean logic correctly.
        """
        expr = "count(i in 1..4)(x[i] > 5 && x[i] < 20) >= 2"
        result = translate_expr_to_lean(expr)

        # count should be expanded to List.sum/List.map
        assert "List.sum" in result
        assert "List.map" in result
        assert "count" not in result

        # Predicate with compound condition
        assert "if" in result
        assert "then 1 else 0" in result

        # All dimensions present
        assert "x.x1" in result
        assert "x.x2" in result
        assert "x.x3" in result
        assert "x.x4" in result

        # Comparison operator preserved
        assert ">= 2" in result

    def test_generate_lean_from_json(self):
        """Test full JSON → Lean4 generation."""
        json_data = {
            "id": "06",
            "title": "Test Chunk",
            "constraints": [
                {"name": "test_constraint", "expr": "x[1] >= 10 && x[2] <= 20"}
            ]
        }
        result = generate_lean_from_json(json_data)

        # Check namespace
        assert "namespace Chunk06" in result
        assert "end Chunk06" in result

        # Check structure
        assert "structure X8" in result
        assert "def unitary" in result
        assert "def domainConstraints" in result

        # Check constraint translated
        assert "x.x1" in result
        assert "x.x2" in result
        assert "∧" in result


# ============================================================================
# Tests for add_constraints.py
# ============================================================================

class TestAddConstraints:
    """Test suite for constraint injection script."""

    def test_detect_chunk_type_external(self):
        """Test heuristic detects 'external' from title."""
        chunk_data = {"id": "01", "title": "External Interface Operator"}
        assert detect_chunk_type(chunk_data) == "external"

    def test_detect_chunk_type_internal(self):
        """Test heuristic detects 'internal' from title."""
        chunk_data = {"id": "02", "title": "Internal Self-Reference Planning"}
        assert detect_chunk_type(chunk_data) == "internal"

    def test_detect_chunk_type_bridge(self):
        """Test heuristic detects 'bridge' from title."""
        chunk_data = {"id": "03", "title": "Bridge Corpus Callosum"}
        assert detect_chunk_type(chunk_data) == "bridge"

    def test_detect_chunk_type_boss(self):
        """Test heuristic detects 'boss' from title or ID."""
        chunk_data1 = {"id": "19", "title": "Something"}
        chunk_data2 = {"id": "20", "title": "Boss Orchestrator"}
        assert detect_chunk_type(chunk_data1) == "boss"
        assert detect_chunk_type(chunk_data2) == "boss"

    def test_detect_chunk_type_default(self):
        """Test heuristic returns 'default' for unknown types."""
        chunk_data = {"id": "99", "title": "Random Chunk"}
        assert detect_chunk_type(chunk_data) == "default"

    def test_count_existing_constraints_empty(self):
        """Test counting with no constraints."""
        chunk_data = {"constraints": []}
        assert count_existing_constraints(chunk_data) == 0

    def test_count_existing_constraints_trivial(self):
        """Test that trivial 'true' constraints are excluded."""
        chunk_data = {
            "constraints": [
                {"name": "trivial", "expr": "true"},
                {"name": "exists", "expr": "exists"}
            ]
        }
        assert count_existing_constraints(chunk_data) == 0

    def test_count_existing_constraints_mixed(self):
        """Test counting non-trivial constraints."""
        chunk_data = {
            "constraints": [
                {"name": "trivial", "expr": "true"},
                {"name": "real1", "expr": "x[1] >= 10"},
                {"name": "real2", "expr": "x[2] <= 20"}
            ]
        }
        assert count_existing_constraints(chunk_data) == 2

    def test_generate_constraint_from_template(self):
        """Test constraint generation from template."""
        template = {
            "id": "range_bound",
            "json_expr": "x[{dim}] >= {min} && x[{dim}] <= {max}",
            "description": "Dimension range constraint",
            "params": ["dim", "min", "max"]
        }
        param_suggestions = {"dim": 1, "min": 5, "max": 50}

        constraint = generate_constraint_from_template(
            template, param_suggestions, "01", []
        )

        assert constraint["name"].startswith("range_bound")
        assert "x[1]" in constraint["expr"]
        assert ">= 5" in constraint["expr"]
        assert "<= 50" in constraint["expr"]
        assert "PHASE3" in constraint["notes"]

    def test_generate_constraint_unique_names(self):
        """Test that generated names are unique when conflicts exist."""
        template = {
            "id": "test",
            "json_expr": "x[{dim}] >= {min}",
            "description": "Test",
            "params": ["dim", "min"]
        }
        existing = ["test_dim1", "test_dim1_1"]

        constraint = generate_constraint_from_template(
            template, {"dim": 1, "min": 10}, "01", existing
        )

        # Should append _2 since _1 is taken
        assert constraint["name"] == "test_dim1_2"

    def test_random_seed_reproducibility(self):
        """
        Test that random.seed() makes constraint generation deterministic.

        This verifies the claim in add_constraints.py line 311.
        """
        template = {
            "id": "test",
            "json_expr": "x[{dim}] >= {min}",
            "description": "Test",
            "params": ["dim", "min"]
        }

        # Generate with seed 42
        random.seed(42)
        c1 = generate_constraint_from_template(template, {}, "01", [])

        # Generate again with seed 42
        random.seed(42)
        c2 = generate_constraint_from_template(template, {}, "01", [])

        # Should be identical
        assert c1["expr"] == c2["expr"]
        assert c1["name"] == c2["name"]

    def test_add_constraints_to_chunk(self):
        """Test adding constraints to a chunk."""
        chunk_data = {
            "id": "01",
            "title": "External Interface",
            "constraints": [
                {"name": "existing", "expr": "x[1] > 0"}
            ]
        }

        templates_data = {
            "templates": [
                {
                    "id": "test_template",
                    "json_expr": "x[{dim}] >= {min}",
                    "description": "Test",
                    "params": ["dim", "min"]
                }
            ],
            "chunk_heuristics": {
                "external": {
                    "preferred_templates": ["test_template"],
                    "param_suggestions": {"test_template": {"dim": 2, "min": 10}}
                },
                "default": {
                    "preferred_templates": [],
                    "param_suggestions": {}
                }
            }
        }

        updated_chunk, num_added = add_constraints_to_chunk(
            chunk_data, templates_data, target_count=2
        )

        assert num_added == 1  # Already had 1, need 1 more
        assert len(updated_chunk["constraints"]) == 2

    def test_add_constraints_already_sufficient(self):
        """Test that no constraints are added if target already met."""
        chunk_data = {
            "id": "01",
            "title": "Test",
            "constraints": [
                {"name": "c1", "expr": "x[1] > 0"},
                {"name": "c2", "expr": "x[2] > 0"}
            ]
        }

        # Fix: Provide complete heuristics structure with required keys
        templates_data = {
            "templates": [],
            "chunk_heuristics": {
                "default": {
                    "preferred_templates": [],
                    "param_suggestions": {}
                }
            }
        }

        updated_chunk, num_added = add_constraints_to_chunk(
            chunk_data, templates_data, target_count=2
        )

        assert num_added == 0
        assert len(updated_chunk["constraints"]) == 2


# ============================================================================
# Integration Tests
# ============================================================================

class TestIntegration:
    """Integration tests for end-to-end workflows."""

    # Note: discover_chunks test removed (Phase 5 - function moved/removed from transpile_to_mzn)

    def test_json_to_mzn_to_lean_consistency(self):
        """
        Test that the same JSON produces consistent outputs in both MZN and Lean.

        This is a smoke test for cross-modal parity.
        """
        json_data = {
            "id": "99",
            "title": "Test Consistency",
            "parameters": {"scaleN": 100},
            "constraints": [
                {"name": "c1", "expr": "x[1] >= 10"},
                {"name": "c2", "expr": "x[2] <= 50"},
                {"name": "c3", "expr": "x[1] + x[2] >= 30"}
            ]
        }

        # Generate both
        mzn_output = generate_mzn_from_json(json_data)
        lean_output = generate_lean_from_json(json_data)

        # Both should have all 3 constraints
        assert mzn_output.count("constraint") >= 4  # 3 domain + 1 unit-sum
        assert lean_output.count("-- constraint:") == 3

        # Both should handle x[1], x[2]
        assert "x[1]" in mzn_output  # MZN keeps array syntax
        assert "x.x1" in lean_output  # Lean converts to struct

        # Both should be non-empty and substantial
        assert len(mzn_output) > 100
        assert len(lean_output) > 200


# ============================================================================
# Property-Based Tests (if hypothesis is available)
# ============================================================================

try:
    from hypothesis import given, strategies as st

    class TestPropertyBased:
        """Property-based tests using Hypothesis."""

        @given(st.integers(min_value=1, max_value=8))
        def test_array_indexing_roundtrip(self, index):
            """Property: x[i] → x.xi translation is consistent."""
            expr = f"x[{index}] > 0"
            lean_result = translate_expr_to_lean(expr)
            assert f"x.x{index}" in lean_result
            assert "x[" not in lean_result

        @given(st.integers(min_value=1, max_value=100))
        def test_numeric_literals_preserved(self, value):
            """Property: Numeric values are preserved in translation."""
            expr = f"x[1] >= {value}"
            mzn_result = translate_expr_to_mzn(expr)
            lean_result = translate_expr_to_lean(expr)
            assert str(value) in mzn_result
            assert str(value) in lean_result

except ImportError:
    # Hypothesis not installed, skip property-based tests
    pass


# ============================================================================
# Performance Tests
# ============================================================================

class TestPerformance:
    """Performance and scalability tests."""

    def test_transpile_mzn_performance(self, benchmark=None):
        """Test MiniZinc transpilation performance."""
        expr = "sum(i in 1..8)(x[i]) >= 50 && forall(i in 1..8)(x[i] >= 0) && x[1] % 2 = 0"

        # If pytest-benchmark is available
        if benchmark:
            result = benchmark(translate_expr_to_mzn, expr)
        else:
            result = translate_expr_to_mzn(expr)

        assert "sum" in result
        assert "mod" in result

    def test_transpile_lean_performance(self, benchmark=None):
        """Test Lean4 transpilation performance."""
        expr = "sum(i in 1..8)(x[i]) >= 50 && forall(i in 1..8)(x[i] >= 0)"

        if benchmark:
            result = benchmark(translate_expr_to_lean, expr)
        else:
            result = translate_expr_to_lean(expr)

        assert "x.x1" in result
        assert "∧" in result


# ============================================================================
# Run with pytest
# ============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
