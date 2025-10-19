"""
Python Testing Analysis Tools

Tools for analyzing test coverage and suggesting testing improvements.
"""

import ast
import re
import asyncio
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional


async def analyze_test_coverage(directory_path: str) -> Dict[str, Any]:
    """
    Analyze test coverage for Python project.

    Args:
        directory_path: Path to project directory

    Returns:
        Dict with coverage analysis
    """
    try:
        # Try to run coverage.py if available
        coverage_data = await _run_coverage_analysis(directory_path)

        if coverage_data:
            return {
                "content": [{
                    "type": "text",
                    "text": _format_coverage_data(coverage_data)
                }],
                "success": True,
                "coverage_data": coverage_data
            }

        # Fallback to manual analysis
        dir_path = Path(directory_path)
        analysis = _manual_coverage_analysis(dir_path)

        return {
            "content": [{
                "type": "text",
                "text": _format_manual_coverage(analysis)
            }],
            "success": True,
            "coverage_analysis": analysis
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Coverage analysis failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_test_patterns(file_path: str, test_type: str = "unit") -> Dict[str, Any]:
    """
    Suggest testing patterns for Python code.

    Args:
        file_path: Path to Python file to test
        test_type: Type of test (unit, integration, functional)

    Returns:
        Dict with testing pattern suggestions
    """
    try:
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')
        tree = ast.parse(content)

        patterns = []

        if test_type == "unit":
            patterns.extend(_suggest_unit_test_patterns(tree, content))
        elif test_type == "integration":
            patterns.extend(_suggest_integration_patterns(tree, content))
        else:  # functional or general
            patterns.extend(_suggest_functional_patterns(tree, content))

        return {
            "content": [{
                "type": "text",
                "text": _format_test_patterns(patterns, test_type)
            }],
            "success": True,
            "patterns": patterns,
            "test_type": test_type
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Test pattern analysis failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def generate_test_stubs(file_path: str, test_framework: str = "pytest") -> Dict[str, Any]:
    """
    Generate test stubs for Python code.

    Args:
        file_path: Path to Python file
        test_framework: Test framework to use (pytest, unittest)

    Returns:
        Dict with generated test stubs
    """
    try:
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')
        tree = ast.parse(content)

        if test_framework == "pytest":
            stubs = _generate_pytest_stubs(tree, path.stem)
        else:  # unittest
            stubs = _generate_unittest_stubs(tree, path.stem)

        return {
            "content": [{
                "type": "text",
                "text": f"✅ Generated test stubs for {path.name}"
            }],
            "success": True,
            "test_stubs": stubs,
            "framework": test_framework
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Test stub generation failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def _run_coverage_analysis(directory: str) -> Optional[Dict[str, Any]]:
    """Run coverage analysis if coverage.py is available."""
    try:
        # Run tests with coverage
        process = await asyncio.create_subprocess_exec(
            "coverage", "run", "-m", "pytest",
            cwd=directory,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )

        await process.communicate()

        # Generate coverage report
        process = await asyncio.create_subprocess_exec(
            "coverage", "report", "--format=json",
            cwd=directory,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )

        stdout, stderr = await process.communicate()

        if process.returncode == 0:
            import json
            return json.loads(stdout.decode())

    except (FileNotFoundError, json.JSONDecodeError):
        pass

    return None


def _manual_coverage_analysis(directory: Path) -> Dict[str, Any]:
    """Manual coverage analysis by examining test files."""
    # Find Python files
    py_files = list(directory.rglob("*.py"))
    test_files = [f for f in py_files if "test" in f.name or f.parent.name == "tests"]
    source_files = [f for f in py_files if f not in test_files and not f.name.startswith("__")]

    # Analyze which functions have corresponding tests
    tested_functions = set()
    untested_functions = []

    for test_file in test_files:
        try:
            content = test_file.read_text(encoding='utf-8')
            tree = ast.parse(content)

            # Find test functions and what they might be testing
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef) and node.name.startswith("test_"):
                    # Extract what function this might be testing
                    tested_func = node.name.replace("test_", "")
                    tested_functions.add(tested_func)
        except:
            continue

    # Find functions in source files
    for source_file in source_files:
        try:
            content = source_file.read_text(encoding='utf-8')
            tree = ast.parse(content)

            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef):
                    if not node.name.startswith("_") and node.name not in tested_functions:
                        untested_functions.append({
                            "function": node.name,
                            "file": str(source_file),
                            "line": node.lineno
                        })
        except:
            continue

    return {
        "total_files": len(source_files),
        "test_files": len(test_files),
        "tested_functions": len(tested_functions),
        "untested_functions": untested_functions,
        "estimated_coverage": len(tested_functions) / (len(tested_functions) + len(untested_functions)) if (tested_functions or untested_functions) else 0
    }


def _suggest_unit_test_patterns(tree: ast.AST, content: str) -> List[Dict[str, Any]]:
    """Suggest unit test patterns for code."""
    patterns = []

    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]

    for func in functions:
        if not func.name.startswith("_"):  # Public functions
            test_suggestions = _analyze_function_for_tests(func, content)
            if test_suggestions:
                patterns.append({
                    "function": func.name,
                    "line": func.lineno,
                    "suggestions": test_suggestions
                })

    return patterns


def _suggest_integration_patterns(tree: ast.AST, content: str) -> List[Dict[str, Any]]:
    """Suggest integration test patterns."""
    patterns = []

    # Look for classes that might need integration testing
    classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]

    for cls in classes:
        if _has_external_dependencies(cls):
            patterns.append({
                "type": "integration",
                "target": cls.name,
                "line": cls.lineno,
                "suggestion": "Test interactions with external dependencies",
                "pattern": "Mock external services and test integration points"
            })

    return patterns


def _suggest_functional_patterns(tree: ast.AST, content: str) -> List[Dict[str, Any]]:
    """Suggest functional/end-to-end test patterns."""
    patterns = []

    # Look for main functions or entry points
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == "main":
            patterns.append({
                "type": "functional",
                "target": "main",
                "line": node.lineno,
                "suggestion": "Test complete workflow from input to output",
                "pattern": "End-to-end testing with realistic data"
            })

    return patterns


def _analyze_function_for_tests(func: ast.FunctionDef, content: str) -> List[str]:
    """Analyze what kinds of tests a function might need."""
    suggestions = []

    # Check if function has parameters
    if func.args.args:
        suggestions.append("Test with various parameter combinations")
        suggestions.append("Test edge cases and boundary values")

    # Check for conditionals
    has_conditions = any(isinstance(node, ast.If) for node in ast.walk(func))
    if has_conditions:
        suggestions.append("Test all conditional branches")

    # Check for loops
    has_loops = any(isinstance(node, (ast.For, ast.While)) for node in ast.walk(func))
    if has_loops:
        suggestions.append("Test loop behavior with empty and multiple items")

    # Check for exception handling
    has_exceptions = any(isinstance(node, (ast.Try, ast.Raise)) for node in ast.walk(func))
    if has_exceptions:
        suggestions.append("Test exception handling and error cases")

    # Check for return statements
    returns = [node for node in ast.walk(func) if isinstance(node, ast.Return)]
    if len(returns) > 1:
        suggestions.append("Test all return paths")

    return suggestions


def _has_external_dependencies(cls: ast.ClassDef) -> bool:
    """Check if class has external dependencies."""
    # Look for method calls that might indicate external dependencies
    for node in ast.walk(cls):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                # Common patterns indicating external dependencies
                if any(keyword in ast.dump(node) for keyword in ["requests", "urllib", "database", "api", "client"]):
                    return True

    return False


def _generate_pytest_stubs(tree: ast.AST, module_name: str) -> str:
    """Generate pytest test stubs."""
    stubs = [
        f'"""',
        f'Test module for {module_name}',
        f'"""',
        f'',
        f'import pytest',
        f'from {module_name} import *',
        f'',
        f''
    ]

    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]

    # Generate function tests
    for func in functions:
        if not func.name.startswith("_"):
            stubs.extend([
                f'def test_{func.name}():',
                f'    """Test {func.name} function."""',
                f'    # TODO: Implement test',
                f'    pass',
                f'',
                f''
            ])

    # Generate class tests
    for cls in classes:
        stubs.extend([
            f'class Test{cls.name}:',
            f'    """Test cases for {cls.name} class."""',
            f'',
            f'    def test_init(self):',
            f'        """Test {cls.name} initialization."""',
            f'        # TODO: Implement test',
            f'        pass',
            f'',
            f''
        ])

    return '\n'.join(stubs)


def _generate_unittest_stubs(tree: ast.AST, module_name: str) -> str:
    """Generate unittest test stubs."""
    stubs = [
        f'"""',
        f'Test module for {module_name}',
        f'"""',
        f'',
        f'import unittest',
        f'from {module_name} import *',
        f'',
        f''
    ]

    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]

    if functions or classes:
        stubs.extend([
            f'class Test{module_name.title()}(unittest.TestCase):',
            f'    """Test cases for {module_name} module."""',
            f'',
            f'    def setUp(self):',
            f'        """Set up test fixtures."""',
            f'        pass',
            f'',
            f''
        ])

        # Generate function tests
        for func in functions:
            if not func.name.startswith("_"):
                stubs.extend([
                    f'    def test_{func.name}(self):',
                    f'        """Test {func.name} function."""',
                    f'        # TODO: Implement test',
                    f'        pass',
                    f'',
                    f''
                ])

    stubs.extend([
        f'if __name__ == "__main__":',
        f'    unittest.main()',
        f''
    ])

    return '\n'.join(stubs)


def _format_coverage_data(coverage_data: Dict[str, Any]) -> str:
    """Format coverage.py results."""
    totals = coverage_data.get("totals", {})
    covered = totals.get("covered_lines", 0)
    missing = totals.get("missing_lines", 0)
    total = covered + missing
    percentage = (covered / total * 100) if total > 0 else 0

    result = [
        f"📊 Test Coverage Report:",
        f"Coverage: {percentage:.1f}% ({covered}/{total} lines)",
    ]

    if percentage >= 90:
        result.append("✅ Excellent coverage")
    elif percentage >= 80:
        result.append("👍 Good coverage")
    elif percentage >= 70:
        result.append("⚠️ Moderate coverage - consider adding tests")
    else:
        result.append("❌ Low coverage - needs more tests")

    return "\n".join(result)


def _format_manual_coverage(analysis: Dict[str, Any]) -> str:
    """Format manual coverage analysis."""
    result = [
        f"📊 Coverage Analysis:",
        f"Source files: {analysis['total_files']}",
        f"Test files: {analysis['test_files']}",
        f"Estimated coverage: {analysis['estimated_coverage']:.1%}"
    ]

    untested = analysis.get('untested_functions', [])
    if untested:
        result.append(f"\n⚠️ {len(untested)} functions appear untested:")
        for func in untested[:5]:  # Show first 5
            result.append(f"  - {func['function']} ({Path(func['file']).name}:{func['line']})")

        if len(untested) > 5:
            result.append(f"  ... and {len(untested) - 5} more")

    return "\n".join(result)


def _format_test_patterns(patterns: List[Dict[str, Any]], test_type: str) -> str:
    """Format test pattern suggestions."""
    if not patterns:
        return f"✅ No additional {test_type} test patterns suggested"

    result = [f"🧪 {test_type.title()} Test Patterns ({len(patterns)}):"]

    for pattern in patterns:
        if 'function' in pattern:
            result.append(f"\n📍 {pattern['function']} (line {pattern['line']}):")
            for suggestion in pattern['suggestions']:
                result.append(f"  • {suggestion}")
        else:
            result.append(f"\n📍 {pattern['target']} (line {pattern['line']}):")
            result.append(f"  • {pattern['suggestion']}")

    return "\n".join(result)