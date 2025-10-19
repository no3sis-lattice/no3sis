"""
Test Analysis Tools

Tools for analyzing test failures and generating insights.
"""

import re
import json
import asyncio
from typing import Dict, Any, List, Optional
from pathlib import Path


async def analyze_failures(failures: List[Dict], language: str = "python") -> Dict[str, Any]:
    """
    Analyze test failures to provide actionable insights.

    Args:
        failures: List of failure dictionaries
        language: Programming language for context

    Returns:
        Dict with failure analysis and suggestions
    """
    try:
        if not failures:
            return {
                "content": [{
                    "type": "text",
                    "text": "✅ No failures to analyze"
                }],
                "success": True,
                "analysis": {"patterns": [], "suggestions": []}
            }

        analysis = {
            "total_failures": len(failures),
            "patterns": _identify_failure_patterns(failures, language),
            "suggestions": [],
            "severity": "medium"
        }

        # Generate suggestions based on patterns
        analysis["suggestions"] = _generate_failure_suggestions(analysis["patterns"], language)

        # Determine severity
        analysis["severity"] = _assess_failure_severity(failures, analysis["patterns"])

        formatted_analysis = _format_failure_analysis(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_analysis
            }],
            "success": True,
            "analysis": analysis
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to analyze failures: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def generate_coverage(test_output: str, framework: str) -> Dict[str, Any]:
    """
    Extract or generate coverage information from test output.

    Args:
        test_output: Raw test execution output
        framework: Test framework used

    Returns:
        Dict with coverage information
    """
    try:
        coverage_info = {}

        if framework == "pytest":
            coverage_info = _extract_pytest_coverage(test_output)
        elif framework in ["jest", "vitest"]:
            coverage_info = _extract_jest_coverage(test_output)
        elif framework == "cargo":
            coverage_info = _extract_cargo_coverage(test_output)
        else:
            coverage_info = _extract_generic_coverage(test_output)

        return {
            "content": [{
                "type": "text",
                "text": _format_coverage_info(coverage_info)
            }],
            "success": True,
            "coverage": coverage_info
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to generate coverage: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def extract_test_info(directory: str) -> Dict[str, Any]:
    """
    Extract information about test structure in a directory.

    Args:
        directory: Directory to analyze

    Returns:
        Dict with test structure information
    """
    try:
        dir_path = Path(directory)
        test_info = {
            "test_files": [],
            "test_count": 0,
            "frameworks": set(),
            "structure": {}
        }

        # Find test files
        test_patterns = [
            "*test*.py", "*spec*.py",  # Python
            "*.test.js", "*.spec.js", "*.test.ts", "*.spec.ts",  # JavaScript/TypeScript
            "*_test.go", "*_test.rs",  # Go, Rust
            "*Test.java", "*Tests.java"  # Java
        ]

        for pattern in test_patterns:
            test_files = list(dir_path.rglob(pattern))
            for test_file in test_files:
                relative_path = test_file.relative_to(dir_path)
                test_info["test_files"].append(str(relative_path))

                # Count tests in file
                test_count = _count_tests_in_file(test_file)
                test_info["test_count"] += test_count

                # Identify framework
                framework = _identify_framework_from_file(test_file)
                if framework:
                    test_info["frameworks"].add(framework)

        test_info["frameworks"] = list(test_info["frameworks"])

        return {
            "content": [{
                "type": "text",
                "text": _format_test_info(test_info)
            }],
            "success": True,
            "test_info": test_info
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to extract test info: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


def _identify_failure_patterns(failures: List[Dict], language: str) -> List[Dict[str, Any]]:
    """Identify common patterns in test failures."""
    patterns = []

    # Error type patterns
    error_types = {}
    for failure in failures:
        error = failure.get("error", "")

        # Common error patterns by language
        if language == "python":
            if "AssertionError" in error:
                error_types["assertion"] = error_types.get("assertion", 0) + 1
            elif "AttributeError" in error:
                error_types["attribute"] = error_types.get("attribute", 0) + 1
            elif "ImportError" in error or "ModuleNotFoundError" in error:
                error_types["import"] = error_types.get("import", 0) + 1
        elif language in ["javascript", "typescript"]:
            if "Expected" in error and "to be" in error:
                error_types["assertion"] = error_types.get("assertion", 0) + 1
            elif "Cannot read property" in error:
                error_types["null_reference"] = error_types.get("null_reference", 0) + 1

    # Convert to pattern objects
    for error_type, count in error_types.items():
        patterns.append({
            "type": error_type,
            "count": count,
            "severity": "high" if count > len(failures) // 2 else "medium"
        })

    return patterns


def _generate_failure_suggestions(patterns: List[Dict], language: str) -> List[str]:
    """Generate suggestions based on failure patterns."""
    suggestions = []

    for pattern in patterns:
        error_type = pattern["type"]
        count = pattern["count"]

        if error_type == "assertion":
            suggestions.append(f"Review {count} assertion failures - check expected vs actual values")
        elif error_type == "attribute":
            suggestions.append(f"Fix {count} attribute errors - check object properties and methods")
        elif error_type == "import":
            suggestions.append(f"Resolve {count} import issues - verify module paths and dependencies")
        elif error_type == "null_reference":
            suggestions.append(f"Handle {count} null reference errors - add null checks")

    if not suggestions:
        suggestions.append("Review individual test failures for specific issues")

    return suggestions


def _assess_failure_severity(failures: List[Dict], patterns: List[Dict]) -> str:
    """Assess overall severity of failures."""
    failure_count = len(failures)

    if failure_count == 0:
        return "none"
    elif failure_count <= 2:
        return "low"
    elif failure_count <= 5:
        return "medium"
    else:
        return "high"


def _extract_pytest_coverage(output: str) -> Dict[str, Any]:
    """Extract coverage from pytest output."""
    coverage = {"available": False, "percentage": None, "details": []}

    # Look for coverage report
    coverage_match = re.search(r'TOTAL\s+\d+\s+\d+\s+(\d+)%', output)
    if coverage_match:
        coverage["available"] = True
        coverage["percentage"] = int(coverage_match.group(1))

    return coverage


def _extract_jest_coverage(output: str) -> Dict[str, Any]:
    """Extract coverage from Jest output."""
    coverage = {"available": False, "percentage": None, "details": []}

    # Look for coverage summary
    if "Coverage summary" in output:
        coverage["available"] = True
        # Extract percentage if available
        percentage_match = re.search(r'All files\s+\|\s+([\d.]+)', output)
        if percentage_match:
            coverage["percentage"] = float(percentage_match.group(1))

    return coverage


def _extract_cargo_coverage(output: str) -> Dict[str, Any]:
    """Extract coverage from cargo output."""
    # Cargo doesn't provide coverage by default
    return {"available": False, "note": "Use cargo-tarpaulin for coverage"}


def _extract_generic_coverage(output: str) -> Dict[str, Any]:
    """Extract generic coverage information."""
    return {"available": False, "note": "Coverage extraction not implemented for this framework"}


def _count_tests_in_file(file_path: Path) -> int:
    """Count tests in a file."""
    try:
        content = file_path.read_text(encoding='utf-8')
        extension = file_path.suffix

        if extension == ".py":
            return len(re.findall(r'def test_\w+|def \w+_test', content))
        elif extension in [".js", ".ts"]:
            return len(re.findall(r'test\s*\(|it\s*\(|describe\s*\(', content))
        elif extension == ".rs":
            return len(re.findall(r'#\[test\]', content))
        elif extension == ".go":
            return len(re.findall(r'func Test\w+', content))
        else:
            return 0

    except:
        return 0


def _identify_framework_from_file(file_path: Path) -> Optional[str]:
    """Identify test framework from file content."""
    try:
        content = file_path.read_text(encoding='utf-8')
        extension = file_path.suffix

        if extension == ".py":
            if "import pytest" in content or "@pytest" in content:
                return "pytest"
            elif "import unittest" in content:
                return "unittest"
        elif extension in [".js", ".ts"]:
            if "jest" in content.lower() or "describe(" in content:
                return "jest"
            elif "vitest" in content.lower():
                return "vitest"

        return None

    except:
        return None


def _format_failure_analysis(analysis: Dict[str, Any]) -> str:
    """Format failure analysis for display."""
    output = []

    output.append(f"🔍 Failure Analysis ({analysis['total_failures']} failures)")
    output.append(f"Severity: {analysis['severity'].upper()}")
    output.append("")

    # Patterns
    if analysis["patterns"]:
        output.append("📊 Failure Patterns:")
        for pattern in analysis["patterns"]:
            output.append(f"  - {pattern['type']}: {pattern['count']} occurrences ({pattern['severity']} priority)")
        output.append("")

    # Suggestions
    if analysis["suggestions"]:
        output.append("💡 Suggested Actions:")
        for i, suggestion in enumerate(analysis["suggestions"], 1):
            output.append(f"  {i}. {suggestion}")

    return "\n".join(output)


def _format_coverage_info(coverage: Dict[str, Any]) -> str:
    """Format coverage information for display."""
    if not coverage.get("available", False):
        note = coverage.get("note", "No coverage information available")
        return f"📊 Coverage: {note}"

    output = ["📊 Test Coverage:"]

    if coverage.get("percentage") is not None:
        percentage = coverage["percentage"]
        emoji = "✅" if percentage >= 80 else "⚠️" if percentage >= 60 else "❌"
        output.append(f"  {emoji} Overall: {percentage}%")

    return "\n".join(output)


def _format_test_info(test_info: Dict[str, Any]) -> str:
    """Format test information for display."""
    output = []

    output.append(f"🧪 Test Structure Analysis")
    output.append(f"Files: {len(test_info['test_files'])}")
    output.append(f"Tests: {test_info['test_count']}")

    if test_info["frameworks"]:
        output.append(f"Frameworks: {', '.join(test_info['frameworks'])}")

    if test_info["test_files"]:
        output.append("")
        output.append("Test Files:")
        for test_file in test_info["test_files"][:10]:  # Show first 10
            output.append(f"  - {test_file}")

        if len(test_info["test_files"]) > 10:
            output.append(f"  ... and {len(test_info['test_files']) - 10} more")

    return "\n".join(output)