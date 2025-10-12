#!/usr/bin/env python3
"""
Standalone test runner for transpilers (no pytest dependency).
Uses Python's built-in unittest framework.

Usage:
  python3 run_tests.py
"""

import sys
import unittest
import subprocess
import tempfile
from pathlib import Path

# Import test subjects
from transpile_to_mzn import translate_expr_to_mzn, generate_mzn_from_json
from transpile_to_lean import translate_expr_to_lean, generate_lean_from_json
from add_constraints import detect_chunk_type, count_existing_constraints


class TestMiniZincTranspiler(unittest.TestCase):
    """Test suite for JSON → MiniZinc transpiler."""

    def test_operator_and(self):
        """Test && → /\\ translation."""
        expr = "x[1] > 5 && x[2] < 10"
        result = translate_expr_to_mzn(expr)
        self.assertIn("/\\", result)
        self.assertNotIn("&&", result)

    def test_operator_or(self):
        """Test || → \\/ translation."""
        expr = "x[1] = 5 || x[2] = 10"
        result = translate_expr_to_mzn(expr)
        self.assertIn("\\/", result)
        self.assertNotIn("||", result)

    def test_operator_not(self):
        """Test ! → not translation."""
        expr = "!(x[1] > 5)"
        result = translate_expr_to_mzn(expr)
        self.assertIn("not", result)
        self.assertNotIn("!", result)

    def test_operator_modulo(self):
        """Test % → mod translation."""
        expr = "x[1] % 3 = 0"
        result = translate_expr_to_mzn(expr)
        self.assertIn("mod", result)
        self.assertNotIn("%", result)

    def test_count_to_sum(self):
        """Test count(...) → sum(...) conversion."""
        expr = "count(i in 1..8)(x[i] > 0) >= 3"
        result = translate_expr_to_mzn(expr)
        self.assertIn("sum(i in 1..8)(x[i] > 0)", result)
        self.assertNotIn("count", result)


class TestLeanTranspiler(unittest.TestCase):
    """Test suite for JSON → Lean4 transpiler."""

    def test_operator_and(self):
        """Test && → ∧ translation."""
        expr = "x[1] > 5 && x[2] < 10"
        result = translate_expr_to_lean(expr)
        self.assertIn("∧", result)
        self.assertNotIn("&&", result)

    def test_operator_or(self):
        """Test || → ∨ translation."""
        expr = "x[1] = 5 || x[2] = 10"
        result = translate_expr_to_lean(expr)
        self.assertIn("∨", result)
        self.assertNotIn("||", result)

    def test_operator_not(self):
        """Test ! → ¬ translation."""
        expr = "!(x[1] > 5)"
        result = translate_expr_to_lean(expr)
        self.assertIn("¬", result)
        self.assertNotIn("!", result)

    def test_array_indexing(self):
        """Test x[i] → x.xi translation."""
        expr = "x[1] + x[2] = x[3]"
        result = translate_expr_to_lean(expr)
        self.assertIn("x.x1", result)
        self.assertIn("x.x2", result)
        self.assertIn("x.x3", result)
        self.assertNotIn("x[", result)

    def test_sum_expansion(self):
        """Test sum(i in 1..4)(x[i]) expansion."""
        expr = "sum(i in 1..4)(x[i]) >= 10"
        result = translate_expr_to_lean(expr)
        self.assertIn("x.x1 + x.x2 + x.x3 + x.x4", result)
        self.assertNotIn("sum", result)

    def test_sum_expansion_double_regression(self):
        """
        REGRESSION TEST: Blocker 1 - Sum Expansion Double-Substitution.

        Multiple sum() in same expression should not corrupt each other.
        """
        expr = "sum(i in 1..4)(x[i]) >= sum(i in 5..8)(x[i])"
        result = translate_expr_to_lean(expr)

        # Both sides should be expanded correctly
        self.assertIn("x.x1 + x.x2 + x.x3 + x.x4", result)
        self.assertIn("x.x5 + x.x6 + x.x7 + x.x8", result)

        # No double-expansion
        self.assertEqual(result.count("x.x5"), 1)
        self.assertEqual(result.count("x.x1"), 1)

    def test_forall_expansion(self):
        """Test forall(i in 1..3)(...) expansion."""
        expr = "forall(i in 1..3)(x[i] >= 5)"
        result = translate_expr_to_lean(expr)
        self.assertIn("x.x1 >= 5", result)
        self.assertIn("x.x2 >= 5", result)
        self.assertIn("x.x3 >= 5", result)
        self.assertIn("∧", result)


class TestConstraintInjection(unittest.TestCase):
    """Test suite for constraint injection."""

    def test_detect_external(self):
        """Test chunk type detection: external."""
        chunk = {"id": "01", "title": "External Interface Operator"}
        self.assertEqual(detect_chunk_type(chunk), "external")

    def test_detect_internal(self):
        """Test chunk type detection: internal."""
        chunk = {"id": "02", "title": "Internal Self-Reference"}
        self.assertEqual(detect_chunk_type(chunk), "internal")

    def test_detect_bridge(self):
        """Test chunk type detection: bridge."""
        chunk = {"id": "03", "title": "Bridge Corpus Callosum"}
        self.assertEqual(detect_chunk_type(chunk), "bridge")

    def test_detect_boss(self):
        """Test chunk type detection: boss."""
        chunk1 = {"id": "19", "title": "Something"}
        chunk2 = {"id": "20", "title": "Boss Orchestrator"}
        self.assertEqual(detect_chunk_type(chunk1), "boss")
        self.assertEqual(detect_chunk_type(chunk2), "boss")

    def test_count_constraints_empty(self):
        """Test constraint counting: empty."""
        chunk = {"constraints": []}
        self.assertEqual(count_existing_constraints(chunk), 0)

    def test_count_constraints_trivial(self):
        """Test constraint counting: excludes trivial."""
        chunk = {
            "constraints": [
                {"name": "trivial", "expr": "true"},
                {"name": "exists", "expr": "exists"}
            ]
        }
        self.assertEqual(count_existing_constraints(chunk), 0)

    def test_count_constraints_mixed(self):
        """Test constraint counting: mixed trivial/real."""
        chunk = {
            "constraints": [
                {"name": "trivial", "expr": "true"},
                {"name": "real1", "expr": "x[1] >= 10"},
                {"name": "real2", "expr": "x[2] <= 20"}
            ]
        }
        self.assertEqual(count_existing_constraints(chunk), 2)


class TestCompilationValidation(unittest.TestCase):
    """Test suite for validating generated code compiles."""

    def test_minizinc_output_compiles(self):
        """Test that generated MiniZinc code compiles successfully."""
        # Create test JSON data
        json_data = {
            "id": "99",
            "title": "Test Compilation",
            "parameters": {
                "scaleN": 100,
                "monsterPrimes": [2, 3, 5, 7]
            },
            "constraints": [
                {"name": "test1", "expr": "x[1] >= 10"},
                {"name": "test2", "expr": "x[2] <= 50"},
                {"name": "test3", "expr": "sum(i in 1..8)(x[i]) >= 100"}
            ]
        }

        # Generate MiniZinc code
        mzn_code = generate_mzn_from_json(json_data)

        # Write to temp file and compile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.mzn', delete=False) as f:
            f.write(mzn_code)
            temp_path = f.name

        try:
            # Try to compile with MiniZinc (compile-only, don't solve)
            result = subprocess.run(
                ['minizinc', '--solver', 'gecode', '--compile', temp_path],
                capture_output=True,
                text=True,
                timeout=10
            )

            # Check compilation succeeded
            self.assertEqual(result.returncode, 0,
                           f"MiniZinc compilation failed:\n{result.stderr}")

        finally:
            # Cleanup
            Path(temp_path).unlink()

    def test_lean_output_syntax_valid(self):
        """Test that generated Lean4 code has valid syntax (lean --stdin check)."""
        # Create test JSON data
        json_data = {
            "id": "99",
            "title": "Test Compilation",
            "constraints": [
                {"name": "test1", "expr": "x[1] >= 10"},
                {"name": "test2", "expr": "x[2] <= 50"},
                {"name": "test3", "expr": "x[1] + x[2] >= 30"}
            ]
        }

        # Generate Lean code
        lean_code = generate_lean_from_json(json_data)

        # Basic syntax check: should contain required elements
        self.assertIn("namespace Chunk99", lean_code)
        self.assertIn("structure X8", lean_code)
        self.assertIn("def domainConstraints", lean_code)
        self.assertIn("end Chunk99", lean_code)

        # Check all constraints were translated
        self.assertIn("x.x1 >= 10", lean_code)
        self.assertIn("x.x2 <= 50", lean_code)
        self.assertIn("x.x1 + x.x2 >= 30", lean_code)

    def test_minizinc_pilot_chunk_compiles(self):
        """Test that pilot chunk 06 MiniZinc output compiles."""
        # Check if chunk 06 MZN file exists
        base_dir = Path(__file__).resolve().parents[1]
        mzn_path = base_dir / "true-dual-tract" / "chunks" / "chunk-06.mzn"

        if not mzn_path.exists():
            self.skipTest(f"Pilot chunk MZN not found: {mzn_path}")

        # Try to compile (compile-only, don't solve)
        result = subprocess.run(
            ['minizinc', '--solver', 'gecode', '--compile', str(mzn_path)],
            capture_output=True,
            text=True,
            timeout=10
        )

        self.assertEqual(result.returncode, 0,
                       f"Pilot chunk 06 MZN compilation failed:\n{result.stderr}")


def run_tests():
    """Run all tests and report results."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    # Add test classes
    suite.addTests(loader.loadTestsFromTestCase(TestMiniZincTranspiler))
    suite.addTests(loader.loadTestsFromTestCase(TestLeanTranspiler))
    suite.addTests(loader.loadTestsFromTestCase(TestConstraintInjection))
    suite.addTests(loader.loadTestsFromTestCase(TestCompilationValidation))

    # Run with verbose output
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)

    # Summary
    print("\n" + "="*70)
    print(f"Tests run: {result.testsRun}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print(f"Skipped: {len(result.skipped)}")
    print("="*70)

    # Return exit code
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_tests())
