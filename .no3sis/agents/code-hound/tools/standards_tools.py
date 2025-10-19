"""
Standards Enforcement Tools

TDD, SOLID, DRY, and KISS principle enforcement with compressed violation detection.
Implements Code Hound's uncompromising standards using 4Q.Zero semantic density.
"""

import re
import ast
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from .analysis_tools import deep_code_analysis

async def enforce_tdd_standards(file_path: str, analysis: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Enforce Test-Driven Development standards with zero tolerance.

    q: What test evidence exists? What's missing?
    a: Compress test compliance into actionable violations
    s: Score TDD adherence (0-100)
    """
    if not analysis:
        analysis = await deep_code_analysis(file_path)

    tdd_report = {
        "file_path": file_path,
        "violations": [],
        "score": 0,
        "evidence": {
            "has_tests": False,
            "test_file_exists": False,
            "red_green_refactor_cycle": False,
            "comprehensive_coverage": False
        }
    }

    path = Path(file_path)
    content = path.read_text() if path.exists() else ""

    # Check if this is a test file
    is_test_file = any(pattern in path.name.lower()
                      for pattern in ['test', 'spec', '_test.py', '.test.js', '_spec.rb'])

    if is_test_file:
        await _analyze_test_file_tdd_compliance(content, analysis, tdd_report)
    else:
        await _check_production_code_tdd_compliance(file_path, content, analysis, tdd_report)

    # Calculate TDD score
    tdd_report["score"] = _calculate_tdd_score(tdd_report["evidence"])

    return tdd_report

async def _analyze_test_file_tdd_compliance(content: str, analysis: Dict[str, Any], report: Dict[str, Any]):
    """Analyze test file for TDD compliance violations."""
    violations = []

    # Evidence: File contains tests
    test_coverage = analysis.get("test_coverage", {})
    if test_coverage.get("has_tests"):
        report["evidence"]["has_tests"] = True
    else:
        violations.append({
            "type": "no_tests_detected",
            "severity": "critical",
            "message": "Test file detected but no test patterns found",
            "line": 1
        })

    # Check for proper test structure
    if not _has_proper_test_structure(content):
        violations.append({
            "type": "improper_test_structure",
            "severity": "major",
            "message": "Tests lack proper Arrange-Act-Assert structure",
            "line": 1
        })

    # Check for test isolation
    if _tests_have_dependencies(content):
        violations.append({
            "type": "test_dependencies",
            "severity": "major",
            "message": "Tests appear to have interdependencies - violates isolation",
            "line": 1
        })

    # Check for mock data usage (Code Hound hates this)
    if _uses_mock_data(content):
        violations.append({
            "type": "mock_data_detected",
            "severity": "critical",
            "message": "MOCK DATA DETECTED - Code Hound despises mock data",
            "line": _find_mock_data_line(content)
        })

    report["violations"].extend(violations)

async def _check_production_code_tdd_compliance(file_path: str, content: str, analysis: Dict[str, Any], report: Dict[str, Any]):
    """Check production code for TDD compliance."""
    violations = []
    path = Path(file_path)

    # Look for corresponding test file
    test_file_patterns = [
        path.parent / f"test_{path.name}",
        path.parent / f"{path.stem}_test{path.suffix}",
        path.parent / "tests" / path.name,
        path.parent.parent / "tests" / path.name
    ]

    test_file_exists = any(test_path.exists() for test_path in test_file_patterns)

    if test_file_exists:
        report["evidence"]["test_file_exists"] = True
    else:
        violations.append({
            "type": "missing_test_file",
            "severity": "critical",
            "message": "No corresponding test file found - TDD requires test-first approach",
            "line": 1
        })

    # Check for untested public methods/functions
    untested_functions = await _find_untested_functions(file_path, content, analysis)
    for func in untested_functions:
        violations.append({
            "type": "untested_function",
            "severity": "major",
            "message": f"Function '{func['name']}' appears untested",
            "line": func.get("line", 1)
        })

    # Check for TODO/FIXME markers (shortcuts)
    shortcuts = _find_tdd_shortcuts(content)
    violations.extend(shortcuts)

    report["violations"].extend(violations)

def _has_proper_test_structure(content: str) -> bool:
    """Check if tests follow Arrange-Act-Assert pattern."""
    # Look for common test patterns
    test_patterns = [
        r'def\s+test_\w+',  # Python
        r'it\s*\(',         # JavaScript/TypeScript
        r'test\s*\(',       # Go
        r'#\[test\]'        # Rust
    ]

    has_tests = any(re.search(pattern, content) for pattern in test_patterns)

    if not has_tests:
        return False

    # Basic structure check - should have setup and assertions
    has_assertions = any(keyword in content.lower() for keyword in
                        ['assert', 'expect', 'should', 'verify'])

    return has_assertions

def _tests_have_dependencies(content: str) -> bool:
    """Detect test interdependencies."""
    # Look for shared state indicators
    shared_state_indicators = [
        r'global\s+\w+',      # Global variables
        r'class\s+\w+.*:\s*\n.*\w+\s*=',  # Class variables
        r'@pytest\.fixture.*scope.*module',  # Module-scoped fixtures
    ]

    return any(re.search(pattern, content, re.MULTILINE) for pattern in shared_state_indicators)

def _uses_mock_data(content: str) -> bool:
    """Detect mock data usage (Code Hound's pet peeve)."""
    mock_indicators = [
        r'\bmock\b',
        r'\bfake\b',
        r'\bstub\b',
        r'MockData',
        r'TestData',
        r'DummyData',
        r'fixture.*mock'
    ]

    return any(re.search(pattern, content, re.IGNORECASE) for pattern in mock_indicators)

def _find_mock_data_line(content: str) -> int:
    """Find line number where mock data is used."""
    lines = content.splitlines()
    for i, line in enumerate(lines, 1):
        if re.search(r'\bmock\b', line, re.IGNORECASE):
            return i
    return 1

async def _find_untested_functions(file_path: str, content: str, analysis: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Find functions that appear to lack tests."""
    structure = analysis.get("structure", {})
    functions = structure.get("functions", [])

    # This is a simplified check - in reality would need to analyze actual test coverage
    untested = []
    for func in functions:
        func_name = func.get("name", "")
        if func_name and not func_name.startswith("_"):  # Skip private functions
            # Simple heuristic: if function name doesn't appear in likely test files
            # This would be more sophisticated in a real implementation
            untested.append(func)

    return untested[:3]  # Limit to avoid spam

def _find_tdd_shortcuts(content: str) -> List[Dict[str, Any]]:
    """Find TDD shortcuts and technical debt markers."""
    shortcuts = []
    lines = content.splitlines()

    for i, line in enumerate(lines, 1):
        line_lower = line.lower()

        if 'todo' in line_lower and 'test' in line_lower:
            shortcuts.append({
                "type": "tdd_todo",
                "severity": "major",
                "message": "TODO marker for testing - complete TDD cycle",
                "line": i
            })

        if 'fixme' in line_lower:
            shortcuts.append({
                "type": "fixme_shortcut",
                "severity": "major",
                "message": "FIXME marker indicates shortcuts taken",
                "line": i
            })

        if 'hack' in line_lower or 'quick' in line_lower:
            shortcuts.append({
                "type": "admitted_shortcut",
                "severity": "critical",
                "message": "Admitted shortcut or hack detected",
                "line": i
            })

    return shortcuts

def _calculate_tdd_score(evidence: Dict[str, bool]) -> int:
    """Calculate TDD compliance score."""
    score = 0

    if evidence.get("has_tests"):
        score += 40
    if evidence.get("test_file_exists"):
        score += 30
    if evidence.get("red_green_refactor_cycle"):
        score += 20
    if evidence.get("comprehensive_coverage"):
        score += 10

    return score

async def check_solid_principles(file_path: str, analysis: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Check SOLID principles compliance with uncompromising standards.

    S - Single Responsibility
    O - Open/Closed
    L - Liskov Substitution
    I - Interface Segregation
    D - Dependency Inversion
    """
    if not analysis:
        analysis = await deep_code_analysis(file_path)

    solid_report = {
        "file_path": file_path,
        "violations": [],
        "scores": {"S": 0, "O": 0, "L": 0, "I": 0, "D": 0},
        "principle_analysis": {}
    }

    content = Path(file_path).read_text() if Path(file_path).exists() else ""

    # Single Responsibility Principle
    await _check_single_responsibility(content, analysis, solid_report)

    # Open/Closed Principle
    await _check_open_closed(content, analysis, solid_report)

    # Liskov Substitution Principle
    await _check_liskov_substitution(content, analysis, solid_report)

    # Interface Segregation Principle
    await _check_interface_segregation(content, analysis, solid_report)

    # Dependency Inversion Principle
    await _check_dependency_inversion(content, analysis, solid_report)

    return solid_report

async def _check_single_responsibility(content: str, analysis: Dict[str, Any], report: Dict[str, Any]):
    """Check Single Responsibility Principle."""
    violations = []
    structure = analysis.get("structure", {})

    # Check classes for multiple responsibilities
    for cls in structure.get("classes", []):
        method_count = cls.get("methods", 0)
        if method_count > 15:  # Threshold for too many methods
            violations.append({
                "type": "srp_violation_large_class",
                "severity": "major",
                "message": f"Class '{cls['name']}' has {method_count} methods - likely multiple responsibilities",
                "line": cls.get("line", 1)
            })

    # Check functions for doing too much
    for func in structure.get("functions", []):
        if func.get("args_count", 0) > 7:  # Too many parameters
            violations.append({
                "type": "srp_violation_complex_function",
                "severity": "medium",
                "message": f"Function '{func['name']}' has too many parameters - doing too much",
                "line": func.get("line", 1)
            })

    report["violations"].extend(violations)
    report["scores"]["S"] = max(0, 100 - len(violations) * 20)

async def _check_open_closed(content: str, analysis: Dict[str, Any], report: Dict[str, Any]):
    """Check Open/Closed Principle."""
    violations = []

    # Look for modification indicators in existing code
    modification_patterns = [
        r'#.*modified',
        r'#.*changed',
        r'#.*updated',
        r'elif.*#.*added'  # New elif branches often indicate O/C violations
    ]

    for pattern in modification_patterns:
        matches = re.finditer(pattern, content, re.IGNORECASE)
        for match in matches:
            line_no = content[:match.start()].count('\n') + 1
            violations.append({
                "type": "ocp_violation_modification",
                "severity": "medium",
                "message": "Evidence of modification to existing code - consider extension instead",
                "line": line_no
            })

    report["violations"].extend(violations)
    report["scores"]["O"] = max(0, 100 - len(violations) * 15)

async def _check_liskov_substitution(content: str, analysis: Dict[str, Any], report: Dict[str, Any]):
    """Check Liskov Substitution Principle."""
    violations = []

    # Look for inheritance issues
    structure = analysis.get("structure", {})
    for cls in structure.get("classes", []):
        inheritance = cls.get("inheritance", [])
        if inheritance:
            # Check for method signature changes (simplified)
            if "override" in content.lower() and "different" in content.lower():
                violations.append({
                    "type": "lsp_violation_signature_change",
                    "severity": "major",
                    "message": f"Class '{cls['name']}' may violate LSP with signature changes",
                    "line": cls.get("line", 1)
                })

    report["violations"].extend(violations)
    report["scores"]["L"] = max(0, 100 - len(violations) * 25)

async def _check_interface_segregation(content: str, analysis: Dict[str, Any], report: Dict[str, Any]):
    """Check Interface Segregation Principle."""
    violations = []

    # Look for large interfaces (language-agnostic patterns)
    interface_patterns = [
        r'interface\s+\w+.*\{[^}]{200,}\}',  # Large interfaces
        r'abstract.*\{[^}]{200,}\}',         # Large abstract classes
    ]

    for pattern in interface_patterns:
        matches = re.finditer(pattern, content, re.DOTALL)
        for match in matches:
            line_no = content[:match.start()].count('\n') + 1
            violations.append({
                "type": "isp_violation_large_interface",
                "severity": "medium",
                "message": "Large interface detected - consider segregation",
                "line": line_no
            })

    report["violations"].extend(violations)
    report["scores"]["I"] = max(0, 100 - len(violations) * 20)

async def _check_dependency_inversion(content: str, analysis: Dict[str, Any], report: Dict[str, Any]):
    """Check Dependency Inversion Principle."""
    violations = []

    # Look for concrete dependencies (simplified heuristic)
    concrete_dependency_patterns = [
        r'new\s+[A-Z]\w+\(',  # Direct instantiation
        r'import\s+.*\.concrete\.',
        r'from\s+.*\.concrete\s+import'
    ]

    for pattern in concrete_dependency_patterns:
        matches = re.finditer(pattern, content)
        for match in matches:
            line_no = content[:match.start()].count('\n') + 1
            violations.append({
                "type": "dip_violation_concrete_dependency",
                "severity": "medium",
                "message": "Direct dependency on concrete implementation detected",
                "line": line_no
            })

    report["violations"].extend(violations)
    report["scores"]["D"] = max(0, 100 - len(violations) * 15)

async def detect_dry_violations(file_path: str, analysis: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Detect DRY principle violations with compressed pattern matching.

    Don't Repeat Yourself - Single source of truth enforcement.
    """
    if not analysis:
        analysis = await deep_code_analysis(file_path)

    dry_report = {
        "file_path": file_path,
        "violations": [],
        "score": 0,
        "duplication_analysis": {}
    }

    content = Path(file_path).read_text() if Path(file_path).exists() else ""

    # Find code duplication
    duplicated_blocks = _find_duplicated_code_blocks(content)
    for dup in duplicated_blocks:
        dry_report["violations"].append({
            "type": "code_duplication",
            "severity": "major",
            "message": f"Duplicated code block found ({dup['lines']} lines)",
            "line": dup["line"]
        })

    # Find repeated constants/magic numbers
    magic_numbers = _find_repeated_magic_numbers(content)
    for magic in magic_numbers:
        dry_report["violations"].append({
            "type": "repeated_magic_number",
            "severity": "medium",
            "message": f"Magic number '{magic['value']}' repeated {magic['count']} times",
            "line": magic["first_line"]
        })

    # Find repeated string literals
    repeated_strings = _find_repeated_strings(content)
    for string in repeated_strings:
        dry_report["violations"].append({
            "type": "repeated_string_literal",
            "severity": "low",
            "message": f"String literal repeated {string['count']} times",
            "line": string["first_line"]
        })

    dry_report["score"] = max(0, 100 - len(dry_report["violations"]) * 10)

    return dry_report

def _find_duplicated_code_blocks(content: str) -> List[Dict[str, Any]]:
    """Find duplicated code blocks."""
    lines = content.splitlines()
    duplications = []

    # Simple algorithm: look for repeated sequences of 3+ lines
    for i in range(len(lines) - 3):
        block = lines[i:i+3]
        block_str = '\n'.join(line.strip() for line in block if line.strip())

        if len(block_str) < 20:  # Skip trivial blocks
            continue

        # Search for this block elsewhere in the file
        for j in range(i + 3, len(lines) - 3):
            other_block = lines[j:j+3]
            other_block_str = '\n'.join(line.strip() for line in other_block if line.strip())

            if block_str == other_block_str:
                duplications.append({
                    "line": i + 1,
                    "lines": 3,
                    "duplicate_at": j + 1
                })
                break

    return duplications[:5]  # Limit to avoid spam

def _find_repeated_magic_numbers(content: str) -> List[Dict[str, Any]]:
    """Find repeated magic numbers."""
    # Find all numbers (excluding common ones like 0, 1, 2)
    numbers = re.findall(r'\b(?:[3-9]|\d{2,})\b', content)
    number_counts = {}
    number_lines = {}

    lines = content.splitlines()
    for i, line in enumerate(lines, 1):
        for num in re.finditer(r'\b(?:[3-9]|\d{2,})\b', line):
            value = num.group()
            number_counts[value] = number_counts.get(value, 0) + 1
            if value not in number_lines:
                number_lines[value] = i

    repeated = []
    for value, count in number_counts.items():
        if count >= 3:  # Repeated 3+ times
            repeated.append({
                "value": value,
                "count": count,
                "first_line": number_lines[value]
            })

    return repeated

def _find_repeated_strings(content: str) -> List[Dict[str, Any]]:
    """Find repeated string literals."""
    # Find string literals
    strings = re.findall(r'["\']([^"\']{5,})["\']', content)
    string_counts = {}
    string_lines = {}

    lines = content.splitlines()
    for i, line in enumerate(lines, 1):
        for match in re.finditer(r'["\']([^"\']{5,})["\']', line):
            value = match.group(1)
            string_counts[value] = string_counts.get(value, 0) + 1
            if value not in string_lines:
                string_lines[value] = i

    repeated = []
    for value, count in string_counts.items():
        if count >= 2:  # Repeated 2+ times
            repeated.append({
                "value": value,
                "count": count,
                "first_line": string_lines[value]
            })

    return repeated[:3]  # Limit to most significant ones

async def scan_shortcuts(file_path: str, analysis: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Scan for shortcuts and technical debt with Code Hound's ruthless standards.

    Zero tolerance for shortcuts, band-aids, or quick fixes.
    """
    if not analysis:
        analysis = await deep_code_analysis(file_path)

    shortcuts_report = {
        "file_path": file_path,
        "violations": [],
        "score": 0,
        "debt_level": "unknown"
    }

    content = Path(file_path).read_text() if Path(file_path).exists() else ""
    lines = content.splitlines()

    # Scan each line for shortcuts
    for i, line in enumerate(lines, 1):
        line_lower = line.lower().strip()

        # TODO/FIXME markers
        if 'todo' in line_lower:
            shortcuts_report["violations"].append({
                "type": "todo_marker",
                "severity": "major",
                "message": "TODO marker indicates incomplete implementation",
                "line": i
            })

        if 'fixme' in line_lower:
            shortcuts_report["violations"].append({
                "type": "fixme_marker",
                "severity": "critical",
                "message": "FIXME marker indicates known broken code",
                "line": i
            })

        # Commented code (shortcuts)
        if line.strip().startswith('#') and any(keyword in line_lower for keyword in
                                               ['def ', 'class ', 'function', 'if ', 'for ']):
            shortcuts_report["violations"].append({
                "type": "commented_code",
                "severity": "medium",
                "message": "Commented-out code should be removed",
                "line": i
            })

        # Quick fixes and hacks
        shortcut_indicators = ['hack', 'quick', 'temp', 'bandaid', 'workaround', 'kludge']
        for indicator in shortcut_indicators:
            if indicator in line_lower:
                shortcuts_report["violations"].append({
                    "type": "admitted_shortcut",
                    "severity": "critical",
                    "message": f"Admitted shortcut or hack: '{indicator}'",
                    "line": i
                })

        # Missing error handling
        if any(risky in line_lower for risky in ['try:', 'catch', 'except']) and 'pass' in line_lower:
            shortcuts_report["violations"].append({
                "type": "empty_exception_handler",
                "severity": "critical",
                "message": "Empty exception handler - shortcuts in error handling",
                "line": i
            })

    # Check for hardcoded values
    hardcoded_violations = _find_hardcoded_values(content)
    shortcuts_report["violations"].extend(hardcoded_violations)

    # Calculate score and debt level
    violation_count = len(shortcuts_report["violations"])
    shortcuts_report["score"] = max(0, 100 - violation_count * 8)

    if violation_count == 0:
        shortcuts_report["debt_level"] = "clean"
    elif violation_count <= 3:
        shortcuts_report["debt_level"] = "low"
    elif violation_count <= 8:
        shortcuts_report["debt_level"] = "medium"
    else:
        shortcuts_report["debt_level"] = "high"

    return shortcuts_report

def _find_hardcoded_values(content: str) -> List[Dict[str, Any]]:
    """Find hardcoded values that should be configurable."""
    violations = []
    lines = content.splitlines()

    # Hardcoded URLs
    url_pattern = r'https?://[^\s\'"]*'
    for i, line in enumerate(lines, 1):
        if re.search(url_pattern, line) and 'localhost' not in line.lower():
            violations.append({
                "type": "hardcoded_url",
                "severity": "medium",
                "message": "Hardcoded URL should be configurable",
                "line": i
            })

    # Hardcoded file paths
    path_pattern = r'["\'][/\\]?(?:[A-Za-z]:|[^"\']*[/\\])[^"\']*["\']'
    for i, line in enumerate(lines, 1):
        if re.search(path_pattern, line) and not any(var in line.lower() for var in ['var', 'config', 'env']):
            violations.append({
                "type": "hardcoded_path",
                "severity": "low",
                "message": "Hardcoded path should use configuration",
                "line": i
            })

    return violations[:3]  # Limit to most critical ones