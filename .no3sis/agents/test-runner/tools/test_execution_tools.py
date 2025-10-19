"""
Test Execution Tools

Core functionality for running tests and parsing results.
"""

import os
import re
import json
import asyncio
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple


async def run_tests(test_spec: str = "", framework: Optional[str] = None, working_dir: Optional[str] = None) -> Dict[str, Any]:
    """
    Run tests based on specification.

    Args:
        test_spec: Test specification (file, pattern, or specific test)
        framework: Test framework to use (auto-detected if not specified)
        working_dir: Working directory for test execution

    Returns:
        Dict with test execution results and analysis
    """
    try:
        cwd = working_dir if working_dir and Path(working_dir).exists() else os.getcwd()

        # Detect test framework if not specified
        if not framework:
            framework = await detect_test_framework(cwd)

        if not framework:
            return {
                "content": [{
                    "type": "text",
                    "text": "❌ Could not detect test framework"
                }],
                "success": False,
                "error": "framework_not_detected"
            }

        # Build test command
        command = _build_test_command(framework, test_spec)

        # Execute tests
        start_time = asyncio.get_event_loop().time()

        process = await asyncio.create_subprocess_exec(
            *command.split(),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            cwd=cwd
        )

        stdout, stderr = await process.communicate()
        execution_time = asyncio.get_event_loop().time() - start_time

        stdout_text = stdout.decode('utf-8', errors='ignore')
        stderr_text = stderr.decode('utf-8', errors='ignore')

        # Parse test results
        parsed_results = await parse_test_output(stdout_text, stderr_text, framework)

        return {
            "content": [{
                "type": "text",
                "text": _format_test_results(parsed_results, execution_time)
            }],
            "success": process.returncode == 0,
            "framework": framework,
            "command": command,
            "execution_time": execution_time,
            "results": parsed_results,
            "raw_stdout": stdout_text,
            "raw_stderr": stderr_text
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Test execution failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def detect_test_framework(directory: str) -> Optional[str]:
    """
    Detect test framework based on project files.

    Args:
        directory: Directory to analyze

    Returns:
        Detected test framework name or None
    """
    dir_path = Path(directory)

    # Check for framework-specific files
    framework_indicators = {
        "pytest": ["pytest.ini", "pyproject.toml", "setup.cfg"],
        "jest": ["jest.config.js", "jest.config.json", "package.json"],
        "vitest": ["vitest.config.js", "vitest.config.ts"],
        "cargo": ["Cargo.toml"],
        "go": ["go.mod"],
        "maven": ["pom.xml"],
        "gradle": ["build.gradle", "build.gradle.kts"]
    }

    for framework, files in framework_indicators.items():
        for file in files:
            if (dir_path / file).exists():
                # Additional validation
                if framework == "jest" and file == "package.json":
                    if _has_jest_dependency(dir_path / file):
                        return "jest"
                else:
                    return framework

    # Check by file extensions and naming patterns
    test_files = list(dir_path.rglob("*test*")) + list(dir_path.rglob("*spec*"))

    for test_file in test_files:
        if test_file.suffix == ".py":
            return "pytest"
        elif test_file.suffix in [".js", ".ts"]:
            return "jest"  # Default for JS/TS
        elif test_file.suffix == ".rs":
            return "cargo"
        elif test_file.suffix == ".go":
            return "go"

    return None


async def parse_test_output(stdout: str, stderr: str, framework: str) -> Dict[str, Any]:
    """
    Parse test output based on framework.

    Args:
        stdout: Standard output from test run
        stderr: Standard error from test run
        framework: Test framework used

    Returns:
        Parsed test results
    """
    if framework == "pytest":
        return _parse_pytest_output(stdout, stderr)
    elif framework in ["jest", "vitest"]:
        return _parse_jest_output(stdout, stderr)
    elif framework == "cargo":
        return _parse_cargo_output(stdout, stderr)
    elif framework == "go":
        return _parse_go_output(stdout, stderr)
    else:
        return _parse_generic_output(stdout, stderr)


def _build_test_command(framework: str, test_spec: str) -> str:
    """Build test command based on framework and specification."""
    commands = {
        "pytest": f"python -m pytest{' ' + test_spec if test_spec else ''}",
        "jest": f"npx jest{' ' + test_spec if test_spec else ''}",
        "vitest": f"npx vitest run{' ' + test_spec if test_spec else ''}",
        "cargo": f"cargo test{' ' + test_spec if test_spec else ''}",
        "go": f"go test{' ' + test_spec if test_spec else ' ./...'}",
        "maven": "mvn test",
        "gradle": "./gradlew test"
    }

    return commands.get(framework, f"echo 'Unknown framework: {framework}'")


def _has_jest_dependency(package_json_path: Path) -> bool:
    """Check if package.json has Jest dependency."""
    try:
        with open(package_json_path) as f:
            package_data = json.load(f)

        dependencies = package_data.get("dependencies", {})
        dev_dependencies = package_data.get("devDependencies", {})
        scripts = package_data.get("scripts", {})

        return (
            "jest" in dependencies or
            "jest" in dev_dependencies or
            any("jest" in script for script in scripts.values())
        )
    except:
        return False


def _parse_pytest_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """Parse pytest output."""
    results = {
        "passed": 0,
        "failed": 0,
        "skipped": 0,
        "failures": [],
        "summary": ""
    }

    # Extract test summary
    summary_match = re.search(r'=+ (.+) =+', stdout)
    if summary_match:
        results["summary"] = summary_match.group(1)

    # Extract counts
    counts_match = re.search(r'(\d+) failed.*?(\d+) passed', stdout)
    if counts_match:
        results["failed"] = int(counts_match.group(1))
        results["passed"] = int(counts_match.group(2))

    # Extract failures
    failures = re.findall(r'FAILED (.+?) - (.+)', stdout)
    for test_name, error_msg in failures:
        results["failures"].append({
            "test": test_name,
            "error": error_msg.strip(),
            "location": _extract_location_from_pytest(stdout, test_name)
        })

    return results


def _parse_jest_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """Parse Jest/Vitest output."""
    results = {
        "passed": 0,
        "failed": 0,
        "skipped": 0,
        "failures": [],
        "summary": ""
    }

    # Extract test summary
    summary_lines = [line for line in stdout.split('\n') if 'Tests:' in line or 'Snapshots:' in line]
    if summary_lines:
        results["summary"] = summary_lines[0]

    # Extract counts from summary
    passed_match = re.search(r'(\d+) passed', stdout)
    failed_match = re.search(r'(\d+) failed', stdout)

    if passed_match:
        results["passed"] = int(passed_match.group(1))
    if failed_match:
        results["failed"] = int(failed_match.group(1))

    # Extract failures
    failure_blocks = re.findall(r'● (.+?)\n\n(.+?)(?=\n●|\nTest Suites:|\n\n$|\Z)', stdout, re.DOTALL)
    for test_name, error_block in failure_blocks:
        results["failures"].append({
            "test": test_name.strip(),
            "error": error_block.strip()[:200] + "..." if len(error_block) > 200 else error_block.strip(),
            "location": _extract_location_from_jest(error_block)
        })

    return results


def _parse_cargo_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """Parse cargo test output."""
    results = {
        "passed": 0,
        "failed": 0,
        "skipped": 0,
        "failures": [],
        "summary": ""
    }

    # Extract test summary
    summary_match = re.search(r'test result: (.+)', stdout)
    if summary_match:
        results["summary"] = summary_match.group(1)

    # Extract counts
    counts_match = re.search(r'(\d+) passed; (\d+) failed', stdout)
    if counts_match:
        results["passed"] = int(counts_match.group(1))
        results["failed"] = int(counts_match.group(2))

    # Extract failures
    failures = re.findall(r'---- (.+?) stdout ----\n(.+?)(?=\n----|\ntest result:|\Z)', stdout, re.DOTALL)
    for test_name, error_msg in failures:
        results["failures"].append({
            "test": test_name,
            "error": error_msg.strip()[:200] + "..." if len(error_msg) > 200 else error_msg.strip(),
            "location": f"test::{test_name}"
        })

    return results


def _parse_go_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """Parse go test output."""
    results = {
        "passed": 0,
        "failed": 0,
        "skipped": 0,
        "failures": [],
        "summary": ""
    }

    lines = stdout.split('\n')

    for line in lines:
        if line.startswith('PASS'):
            results["passed"] += 1
        elif line.startswith('FAIL'):
            results["failed"] += 1
            # Extract test name and package
            parts = line.split()
            if len(parts) >= 2:
                results["failures"].append({
                    "test": parts[1],
                    "error": line,
                    "location": parts[1] if len(parts) >= 2 else "unknown"
                })

    if results["passed"] > 0 or results["failed"] > 0:
        results["summary"] = f"{results['passed']} passed, {results['failed']} failed"

    return results


def _parse_generic_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """Parse generic test output."""
    return {
        "passed": stdout.count("PASS") + stdout.count("✓"),
        "failed": stdout.count("FAIL") + stdout.count("✗"),
        "skipped": stdout.count("SKIP"),
        "failures": [],
        "summary": "Generic test output parsed",
        "raw_output": stdout[:500] + "..." if len(stdout) > 500 else stdout
    }


def _extract_location_from_pytest(output: str, test_name: str) -> str:
    """Extract file location from pytest output."""
    # Look for file:line pattern near the test name
    pattern = rf'{re.escape(test_name)}.*?(\S+\.py:\d+)'
    match = re.search(pattern, output)
    return match.group(1) if match else "location unknown"


def _extract_location_from_jest(error_block: str) -> str:
    """Extract file location from Jest error block."""
    # Look for file:line:column pattern
    pattern = r'at .+ \((.+\.(?:js|ts|jsx|tsx):\d+:\d+)\)'
    match = re.search(pattern, error_block)
    return match.group(1) if match else "location unknown"


def _format_test_results(results: Dict[str, Any], execution_time: float) -> str:
    """Format test results for display."""
    output = []

    # Summary line
    passed = results.get("passed", 0)
    failed = results.get("failed", 0)
    skipped = results.get("skipped", 0)

    output.append(f"✅ Passing: {passed} tests")
    output.append(f"❌ Failing: {failed} tests")
    if skipped > 0:
        output.append(f"⏭️ Skipped: {skipped} tests")

    output.append(f"⏱️ Execution time: {execution_time:.2f}s")
    output.append("")

    # Failure details
    failures = results.get("failures", [])
    for i, failure in enumerate(failures, 1):
        output.append(f"Failed Test {i}: {failure['test']}")
        output.append(f"Location: {failure.get('location', 'unknown')}")
        output.append(f"Error: {failure['error']}")
        output.append("")

    if failed > 0:
        output.append("Returning control for fixes.")

    return "\n".join(output)