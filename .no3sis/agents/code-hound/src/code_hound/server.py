#!/usr/bin/env python3
"""
Code Hound MCP Server
=====================

MCP server for static analysis, TDD/SOLID/DRY enforcement, and quality metrics.

Architecture:
    Claude Code → MCP Protocol → Code Hound → ruff/mypy/bandit → Analysis Results
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
    name="code-hound",
    instructions="Code Hound MCP Server - Static analysis and quality enforcement"
)


# ============================================================================
# Helper Functions
# ============================================================================

def run_linter(command: List[str], cwd: Optional[str] = None) -> Dict[str, Any]:
    """
    Run a linter command and return structured results.

    Args:
        command: Command and arguments to run
        cwd: Working directory

    Returns:
        Dict with stdout, stderr, returncode
    """
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            cwd=cwd,
            timeout=60
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
async def comprehensive_code_review(
    file_path: str,
    language: str,
    review_type: str = "full"
) -> str:
    """
    Perform comprehensive code review using ruff, mypy, and other linters.

    Args:
        file_path: Path to file or directory
        language: Programming language (python, rust, typescript, etc.)
        review_type: Review depth ("full", "quick", "security")

    Returns:
        JSON string with ReviewReport containing quality scores, violations, suggestions
    """
    path = Path(file_path)

    if not path.exists():
        result = {
            "success": False,
            "error": f"Path does not exist: {file_path}",
            "language": language,
            "review_type": review_type
        }
        return json.dumps(result, indent=2)

    violations = []
    suggestions = []
    quality_score = 100.0

    try:
        if language == "python":
            # Run ruff (linting)
            ruff_result = run_linter(["ruff", "check", str(path), "--output-format=json"])

            if ruff_result.get("success"):
                try:
                    ruff_issues = json.loads(ruff_result["stdout"]) if ruff_result["stdout"] else []
                    violations.extend(ruff_issues)
                    quality_score -= min(len(ruff_issues) * 2, 40)  # Max -40 points for linting
                except json.JSONDecodeError:
                    # Ruff might return empty output if no issues
                    pass

            # Run mypy (type checking) if full review
            if review_type == "full":
                mypy_result = run_linter(["mypy", str(path), "--strict"])
                if mypy_result.get("stderr"):
                    mypy_errors = mypy_result["stderr"].split("\n")
                    violations.extend([{"tool": "mypy", "message": line} for line in mypy_errors if line.strip()])
                    quality_score -= min(len(mypy_errors) * 1.5, 30)  # Max -30 points for typing

            # Run bandit (security) if security review
            if review_type == "security" or review_type == "full":
                bandit_result = run_linter(["bandit", "-r", str(path), "-f", "json"])
                if bandit_result.get("stdout"):
                    try:
                        bandit_issues = json.loads(bandit_result["stdout"])
                        security_issues = bandit_issues.get("results", [])
                        violations.extend(security_issues)
                        quality_score -= min(len(security_issues) * 3, 30)  # Max -30 points for security
                    except json.JSONDecodeError:
                        pass

        else:
            # Other languages not yet implemented
            suggestions.append(f"Code review for {language} not yet implemented")

        result = {
            "success": True,
            "file_path": str(path.absolute()),
            "language": language,
            "review_type": review_type,
            "quality_score": max(quality_score, 0),
            "violations_count": len(violations),
            "violations": violations[:20],  # Limit to first 20 for readability
            "suggestions": suggestions,
            "message": f"Review complete: {len(violations)} issues found (quality score: {quality_score:.1f}/100)"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "file_path": file_path,
            "error": str(e),
            "message": f"Review failed: {e}"
        }
        return json.dumps(result, indent=2)


@mcp.tool()
async def enforce_coding_standards(
    file_path: str,
    standards: List[str]
) -> str:
    """
    Enforce specific coding standards (TDD, SOLID, DRY, KISS).

    Args:
        file_path: File or directory to check
        standards: Standards to enforce (e.g., ["TDD", "SOLID", "DRY"])

    Returns:
        JSON string with EnforcementReport containing violations, severity, fix suggestions
    """
    path = Path(file_path)

    if not path.exists():
        result = {
            "success": False,
            "error": f"Path does not exist: {file_path}",
            "standards": standards
        }
        return json.dumps(result, indent=2)

    violations = []

    try:
        # TDD: Check for test coverage
        if "TDD" in standards:
            if path.is_file():
                # Check if there's a corresponding test file
                test_file_candidates = [
                    path.parent / f"test_{path.name}",
                    path.parent / "tests" / f"test_{path.name}",
                    path.parent.parent / "tests" / f"test_{path.name}"
                ]

                has_test = any(candidate.exists() for candidate in test_file_candidates)

                if not has_test:
                    violations.append({
                        "standard": "TDD",
                        "severity": "medium",
                        "message": f"No test file found for {path.name}",
                        "suggestion": f"Create test_{path.name} to follow TDD principles"
                    })

        # SOLID: Basic checks (requires AST analysis for full implementation)
        if "SOLID" in standards:
            if path.suffix == ".py":
                content = path.read_text()
                lines = content.split("\n")

                # Simple heuristic: very long files might violate SRP
                if len(lines) > 300:
                    violations.append({
                        "standard": "SOLID (SRP)",
                        "severity": "low",
                        "message": f"File has {len(lines)} lines (>300 threshold)",
                        "suggestion": "Consider splitting into smaller modules (Single Responsibility Principle)"
                    })

        # DRY: Basic duplicate detection (placeholder)
        if "DRY" in standards:
            violations.append({
                "standard": "DRY",
                "severity": "info",
                "message": "DRY enforcement requires AST analysis (not yet implemented)",
                "suggestion": "Use ruff or pylint for duplicate code detection"
            })

        # KISS: Complexity metrics (placeholder)
        if "KISS" in standards:
            violations.append({
                "standard": "KISS",
                "severity": "info",
                "message": "KISS enforcement requires complexity metrics (see calculate_complexity_metrics)",
                "suggestion": "Use radon or mccabe for cyclomatic complexity"
            })

        result = {
            "success": True,
            "file_path": str(path.absolute()),
            "standards": standards,
            "violations_count": len(violations),
            "violations": violations,
            "message": f"Standards enforcement complete: {len(violations)} violations found"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "file_path": file_path,
            "error": str(e),
            "message": f"Standards enforcement failed: {e}"
        }
        return json.dumps(result, indent=2)


@mcp.tool()
async def detect_code_smells(
    file_path: str,
    language: str
) -> str:
    """
    Detect code smells and anti-patterns.

    Args:
        file_path: File or directory
        language: Programming language

    Returns:
        JSON string with SmellReport containing detected smells, severity, refactoring suggestions
    """
    path = Path(file_path)

    if not path.exists():
        result = {
            "success": False,
            "error": f"Path does not exist: {file_path}",
            "language": language
        }
        return json.dumps(result, indent=2)

    smells = []

    try:
        if language == "python":
            # Use ruff with specific rules for code smells
            ruff_result = run_linter([
                "ruff", "check", str(path),
                "--select", "C,N,D,E,F,I,PL",  # Complexity, naming, docstrings, etc.
                "--output-format=json"
            ])

            if ruff_result.get("success") or ruff_result.get("stdout"):
                try:
                    ruff_issues = json.loads(ruff_result["stdout"]) if ruff_result["stdout"] else []

                    # Categorize by smell type
                    for issue in ruff_issues:
                        code = issue.get("code", "")
                        smell_type = "unknown"

                        if code.startswith("C"):
                            smell_type = "complexity"
                        elif code.startswith("N"):
                            smell_type = "naming"
                        elif code.startswith("D"):
                            smell_type = "documentation"
                        elif code.startswith("PL"):
                            smell_type = "pylint"

                        smells.append({
                            "type": smell_type,
                            "code": code,
                            "message": issue.get("message", ""),
                            "location": issue.get("location", {}),
                            "severity": "medium"
                        })

                except json.JSONDecodeError:
                    pass

            # Additional heuristics
            if path.is_file() and path.suffix == ".py":
                content = path.read_text()

                # Long functions (simple regex-based detection)
                import re
                function_pattern = r"^def\s+\w+.*?(?=^def\s|\Z)"
                functions = re.findall(function_pattern, content, re.MULTILINE | re.DOTALL)

                for func in functions:
                    func_lines = len(func.split("\n"))
                    if func_lines > 50:
                        smells.append({
                            "type": "long_function",
                            "message": f"Function has {func_lines} lines (>50 threshold)",
                            "severity": "medium",
                            "suggestion": "Consider breaking into smaller functions"
                        })

        else:
            smells.append({
                "type": "unsupported",
                "message": f"Code smell detection for {language} not yet implemented",
                "severity": "info"
            })

        result = {
            "success": True,
            "file_path": str(path.absolute()),
            "language": language,
            "smells_count": len(smells),
            "smells": smells[:30],  # Limit output
            "message": f"Smell detection complete: {len(smells)} smells found"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "file_path": file_path,
            "error": str(e),
            "message": f"Smell detection failed: {e}"
        }
        return json.dumps(result, indent=2)


# ============================================================================
# Placeholder implementations for remaining tools (Tier 2)
# ============================================================================

@mcp.tool()
async def project_quality_audit(
    directory: str,
    language: str
) -> str:
    """
    Audit entire project for quality metrics and compliance.

    Args:
        directory: Project root directory
        language: Primary language

    Returns:
        JSON string with AuditReport
    """
    result = {
        "success": False,
        "message": "Project quality audit not yet implemented (Tier 2)",
        "directory": directory,
        "language": language
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def calculate_complexity_metrics(
    file_path: str,
    language: str
) -> str:
    """
    Calculate cyclomatic complexity and other metrics.

    Args:
        file_path: File or directory
        language: Programming language

    Returns:
        JSON string with ComplexityMetrics
    """
    result = {
        "success": False,
        "message": "Complexity metrics not yet implemented (Tier 2)",
        "file_path": file_path,
        "language": language
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def get_synapse_patterns() -> str:
    """
    Retrieve No3sis-specific code patterns and best practices.

    Returns:
        JSON string with No3sis patterns
    """
    result = {
        "success": False,
        "message": "No3sis patterns integration not yet implemented (Tier 2)",
        "patterns": []
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
