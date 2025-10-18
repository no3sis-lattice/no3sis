#!/usr/bin/env python3
"""
Test Runner MCP Server
=======================

MCP server for multi-framework test execution, failure analysis, and coverage reporting.

Architecture:
    Claude Code → MCP Protocol → Test Runner → pytest/jest/cargo → Test Results
"""

import asyncio
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

from mcp.server import FastMCP


# ============================================================================
# Create FastMCP server instance
# ============================================================================

mcp = FastMCP(
    name="test-runner",
    instructions="Test Runner MCP Server - Multi-framework test execution and analysis"
)


# ============================================================================
# Helper Functions
# ============================================================================

def run_command(command: List[str], cwd: Optional[str] = None, timeout: int = 120) -> Dict[str, Any]:
    """
    Run a command and return structured results.

    Args:
        command: Command and arguments to run
        cwd: Working directory
        timeout: Timeout in seconds

    Returns:
        Dict with stdout, stderr, returncode
    """
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            cwd=cwd,
            timeout=timeout
        )

        return {
            "stdout": result.stdout,
            "stderr": result.stderr,
            "returncode": result.returncode,
            "success": result.returncode == 0
        }

    except subprocess.TimeoutExpired:
        return {
            "error": "Command timed out",
            "command": " ".join(command),
            "timeout": timeout,
            "success": False
        }
    except FileNotFoundError:
        return {
            "error": f"Command not found: {command[0]}",
            "suggestion": f"Install {command[0]} to enable this feature",
            "success": False
        }
    except Exception as e:
        return {
            "error": str(e),
            "success": False
        }


# ============================================================================
# MCP Tool Implementations (MVP: 3 critical tools)
# ============================================================================

@mcp.tool()
async def execute_tests(
    test_spec: str,
    framework: Optional[str] = None,
    working_dir: Optional[str] = None
) -> str:
    """
    Execute tests using detected or specified framework.

    Args:
        test_spec: Test path or pattern
            - File: "tests/test_priority_queue.py"
            - Directory: "tests/"
            - Pattern: "tests/**/test_*.py"
        framework: Test framework (auto-detected if omitted)
            - "pytest" (Python)
            - "jest" (JavaScript/TypeScript)
            - "cargo" (Rust)
            - "go" (Go)
        working_dir: Working directory (defaults to current)

    Returns:
        JSON string with TestResult: pass/fail counts, output, failures
    """
    try:
        test_path = Path(test_spec)
        work_dir = working_dir or str(Path.cwd())

        # Auto-detect framework if not specified
        if not framework:
            if test_path.suffix == ".py" or (test_path.is_dir() and any(test_path.glob("test_*.py"))):
                framework = "pytest"
            elif test_path.suffix in [".js", ".ts"] or (test_path.is_dir() and any(test_path.glob("*.test.js"))):
                framework = "jest"
            elif test_path.name == "Cargo.toml" or (test_path.parent / "Cargo.toml").exists():
                framework = "cargo"
            else:
                framework = "pytest"  # Default fallback

        # Build command based on framework
        if framework == "pytest":
            command = ["pytest", test_spec, "-v", "--tb=short", "--no-header"]
        elif framework == "jest":
            command = ["jest", test_spec, "--verbose"]
        elif framework == "cargo":
            command = ["cargo", "test"]
        elif framework == "go":
            command = ["go", "test", "-v", test_spec]
        else:
            result = {
                "success": False,
                "error": f"Unsupported framework: {framework}",
                "test_spec": test_spec
            }
            return json.dumps(result, indent=2)

        # Execute tests
        test_result = run_command(command, cwd=work_dir, timeout=180)

        # Parse output (simplified parsing)
        passed = 0
        failed = 0
        failures = []

        if framework == "pytest":
            output = test_result.get("stdout", "")
            for line in output.split("\n"):
                if "passed" in line.lower():
                    import re
                    match = re.search(r"(\d+) passed", line)
                    if match:
                        passed = int(match.group(1))
                if "failed" in line.lower():
                    import re
                    match = re.search(r"(\d+) failed", line)
                    if match:
                        failed = int(match.group(1))

            # Extract failure details
            if failed > 0:
                failure_section = False
                current_failure = []
                for line in output.split("\n"):
                    if "FAILED" in line:
                        failure_section = True
                        current_failure = [line]
                    elif failure_section:
                        current_failure.append(line)
                        if line.strip().startswith("="):
                            failures.append("\n".join(current_failure))
                            current_failure = []
                            failure_section = False

        result = {
            "success": test_result.get("success", False),
            "test_spec": test_spec,
            "framework": framework,
            "passed": passed,
            "failed": failed,
            "total": passed + failed,
            "failures": failures[:10],  # Limit to first 10 failures
            "output": test_result.get("stdout", "")[:5000],  # Limit output length
            "stderr": test_result.get("stderr", "")[:2000],
            "message": f"Tests executed: {passed} passed, {failed} failed"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "test_spec": test_spec,
            "error": str(e),
            "message": f"Test execution failed: {e}"
        }
        return json.dumps(result, indent=2)


@mcp.tool()
async def detect_test_framework(directory: str) -> str:
    """
    Auto-detect test framework from project structure.

    Args:
        directory: Project directory

    Returns:
        JSON string with FrameworkInfo: detected framework, confidence, config files
    """
    try:
        project_dir = Path(directory)

        if not project_dir.exists():
            result = {
                "success": False,
                "error": f"Directory does not exist: {directory}"
            }
            return json.dumps(result, indent=2)

        frameworks = []

        # Check for pytest
        if (project_dir / "pytest.ini").exists() or \
           (project_dir / "pyproject.toml").exists() or \
           any(project_dir.rglob("test_*.py")):
            frameworks.append({
                "framework": "pytest",
                "confidence": 0.95,
                "evidence": ["test_*.py files", "pytest.ini or pyproject.toml"]
            })

        # Check for jest
        if (project_dir / "jest.config.js").exists() or \
           any(project_dir.rglob("*.test.js")) or \
           any(project_dir.rglob("*.test.ts")):
            frameworks.append({
                "framework": "jest",
                "confidence": 0.90,
                "evidence": ["*.test.js files", "jest.config.js"]
            })

        # Check for cargo (Rust)
        if (project_dir / "Cargo.toml").exists():
            frameworks.append({
                "framework": "cargo",
                "confidence": 0.99,
                "evidence": ["Cargo.toml"]
            })

        # Check for Go
        if any(project_dir.rglob("*_test.go")):
            frameworks.append({
                "framework": "go",
                "confidence": 0.90,
                "evidence": ["*_test.go files"]
            })

        # Sort by confidence
        frameworks.sort(key=lambda x: x["confidence"], reverse=True)

        result = {
            "success": True,
            "directory": str(project_dir.absolute()),
            "frameworks": frameworks,
            "primary_framework": frameworks[0] if frameworks else None,
            "message": f"Detected {len(frameworks)} test framework(s)"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "directory": directory,
            "error": str(e),
            "message": f"Framework detection failed: {e}"
        }
        return json.dumps(result, indent=2)


@mcp.tool()
async def analyze_test_failures(
    failures: List[str],
    language: str
) -> str:
    """
    Analyze test failures and suggest fixes.

    Args:
        failures: Failure data from execute_tests (list of failure strings)
        language: Programming language

    Returns:
        JSON string with AnalysisReport: root causes, fix suggestions, patterns
    """
    try:
        analyses = []

        for failure in failures[:10]:  # Analyze first 10 failures
            analysis = {
                "failure": failure[:500],  # Truncate long failures
                "root_cause": "unknown",
                "suggestions": [],
                "pattern": "unknown"
            }

            # Simple pattern matching for common failure types
            if "AssertionError" in failure:
                analysis["root_cause"] = "Assertion failed"
                analysis["pattern"] = "assertion_error"
                analysis["suggestions"] = [
                    "Check expected vs actual values",
                    "Verify test logic and assumptions"
                ]

            elif "AttributeError" in failure:
                analysis["root_cause"] = "Missing attribute or method"
                analysis["pattern"] = "attribute_error"
                analysis["suggestions"] = [
                    "Verify object has expected attribute",
                    "Check for typos in attribute name",
                    "Ensure proper object initialization"
                ]

            elif "TypeError" in failure:
                analysis["root_cause"] = "Type mismatch"
                analysis["pattern"] = "type_error"
                analysis["suggestions"] = [
                    "Check argument types",
                    "Verify function signature",
                    "Add type hints for clarity"
                ]

            elif "ImportError" in failure or "ModuleNotFoundError" in failure:
                analysis["root_cause"] = "Missing dependency"
                analysis["pattern"] = "import_error"
                analysis["suggestions"] = [
                    "Install missing package",
                    "Check import path",
                    "Verify PYTHONPATH"
                ]

            elif "FileNotFoundError" in failure:
                analysis["root_cause"] = "Missing file"
                analysis["pattern"] = "file_not_found"
                analysis["suggestions"] = [
                    "Check file path",
                    "Create missing file",
                    "Verify working directory"
                ]

            else:
                analysis["suggestions"] = [
                    "Review stack trace for clues",
                    "Check recent code changes",
                    "Run test in isolation"
                ]

            analyses.append(analysis)

        # Summary statistics
        patterns = {}
        for analysis in analyses:
            pattern = analysis["pattern"]
            patterns[pattern] = patterns.get(pattern, 0) + 1

        result = {
            "success": True,
            "language": language,
            "failures_analyzed": len(analyses),
            "analyses": analyses,
            "pattern_summary": patterns,
            "message": f"Analyzed {len(analyses)} test failures"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "language": language,
            "error": str(e),
            "message": f"Failure analysis failed: {e}"
        }
        return json.dumps(result, indent=2)


# ============================================================================
# Placeholder implementations for remaining tools (Tier 2)
# ============================================================================

@mcp.tool()
async def generate_coverage_report(
    test_output: str,
    framework: str
) -> str:
    """
    Parse test output and generate coverage metrics.

    Args:
        test_output: Raw test output
        framework: Test framework

    Returns:
        JSON string with CoverageReport
    """
    result = {
        "success": False,
        "message": "Coverage report generation not yet implemented (Tier 2)",
        "framework": framework
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def query_test_patterns(
    query: str,
    language: str
) -> str:
    """
    Search for test patterns and best practices.

    Args:
        query: Search query
        language: Programming language

    Returns:
        JSON string with test patterns
    """
    result = {
        "success": False,
        "message": "Test pattern search not yet implemented (Tier 2)",
        "query": query,
        "language": language
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def search_test_solutions(
    error_message: str,
    framework: str
) -> str:
    """
    Search knowledge base for solutions to test failures.

    Args:
        error_message: Error message from failed test
        framework: Test framework

    Returns:
        JSON string with solutions
    """
    result = {
        "success": False,
        "message": "Test solution search not yet implemented (Tier 2)",
        "error_message": error_message[:200],
        "framework": framework
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def run_test_suite(
    suite_name: str,
    options: dict
) -> str:
    """
    Run a predefined test suite with options.

    Args:
        suite_name: Suite identifier (e.g., "unit", "integration", "all")
        options: Test options (parallel, verbose, fail_fast)

    Returns:
        JSON string with SuiteResult
    """
    result = {
        "success": False,
        "message": "Test suite execution not yet implemented (Tier 2)",
        "suite_name": suite_name,
        "options": options
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def extract_test_metadata(directory: str) -> str:
    """
    Extract metadata about tests (count, coverage, frameworks).

    Args:
        directory: Project directory

    Returns:
        JSON string with TestMetadata
    """
    result = {
        "success": False,
        "message": "Test metadata extraction not yet implemented (Tier 2)",
        "directory": directory
    }
    return json.dumps(result, indent=2)


# ============================================================================
# Main entry point
# ============================================================================

async def main():
    """Main entry point: runs MCP server via stdio."""
    await mcp.run_stdio_async()


if __name__ == "__main__":
    asyncio.run(main())
