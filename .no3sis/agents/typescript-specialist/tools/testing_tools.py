"""
TypeScript Testing Tools

Tools for analyzing test coverage, generating test stubs, and suggesting
testing patterns for TypeScript/JavaScript projects.
"""

import json
import re
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional


async def analyze_test_coverage(directory_path: str) -> Dict[str, Any]:
    """
    Analyze test coverage for TypeScript/JavaScript project.

    Args:
        directory_path: Path to project directory

    Returns:
        Dict with test coverage analysis results
    """
    try:
        path = Path(directory_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Directory not found: {directory_path}"
                }],
                "success": False,
                "error": "directory_not_found"
            }

        analysis = await _analyze_project_testing(str(path))

        formatted_output = _format_test_coverage_results(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": analysis,
            "directory_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Test coverage analysis failed for {directory_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def generate_test_stubs(file_path: str, test_framework: str = "jest") -> Dict[str, Any]:
    """
    Generate test stubs for TypeScript/JavaScript files.

    Args:
        file_path: Path to source file
        test_framework: Testing framework (jest, vitest, cypress, playwright)

    Returns:
        Dict with generated test stubs
    """
    try:
        path = Path(file_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ File not found: {file_path}"
                }],
                "success": False,
                "error": "file_not_found"
            }

        if not path.suffix in ['.ts', '.tsx', '.js', '.jsx']:
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ Not a TypeScript/JavaScript file: {file_path}"
                }],
                "success": False,
                "error": "not_typescript_file"
            }

        content = path.read_text(encoding='utf-8')

        stubs = await _generate_test_stubs_for_file(content, str(path), test_framework)

        formatted_output = _format_test_stubs(stubs, test_framework)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "stubs": stubs,
            "framework": test_framework,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Test stub generation failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_test_patterns(file_path: str, test_type: str = "unit") -> Dict[str, Any]:
    """
    Suggest testing patterns and best practices.

    Args:
        file_path: Path to file to analyze for test patterns
        test_type: Type of test (unit, integration, e2e)

    Returns:
        Dict with testing pattern suggestions
    """
    try:
        path = Path(file_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ File not found: {file_path}"
                }],
                "success": False,
                "error": "file_not_found"
            }

        content = path.read_text(encoding='utf-8')

        suggestions = await _analyze_test_patterns(content, str(path), test_type)

        formatted_output = _format_test_pattern_suggestions(suggestions, test_type)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "suggestions": suggestions,
            "test_type": test_type,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Test pattern analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

async def _analyze_project_testing(project_path: str) -> Dict[str, Any]:
    """Analyze testing setup and coverage for the entire project."""
    path = Path(project_path)

    # Detect testing frameworks
    frameworks = await _detect_testing_frameworks(path)

    # Find test files
    test_files = _find_test_files(path)

    # Analyze test structure
    test_structure = _analyze_test_structure(test_files)

    # Try to get coverage report
    coverage_report = await _try_get_coverage_report(path)

    # Analyze source files for testability
    source_files = list(path.glob('**/*.{js,jsx,ts,tsx}'))
    source_files = [f for f in source_files if not _is_test_file(f)]
    testability = _analyze_testability(source_files[:20])  # Limit to first 20 files

    return {
        "frameworks": frameworks,
        "test_files": {
            "count": len(test_files),
            "files": [str(f.relative_to(path)) for f in test_files[:10]]  # Limit display
        },
        "test_structure": test_structure,
        "coverage": coverage_report,
        "testability": testability,
        "recommendations": _generate_testing_recommendations(
            frameworks, len(test_files), len(source_files), coverage_report
        )
    }


async def _detect_testing_frameworks(path: Path) -> Dict[str, Any]:
    """Detect which testing frameworks are configured."""
    package_json = path / "package.json"
    frameworks = {
        "jest": False,
        "vitest": False,
        "cypress": False,
        "playwright": False,
        "mocha": False,
        "jasmine": False
    }

    config_files = {
        "jest": ["jest.config.js", "jest.config.ts", "jest.config.json"],
        "vitest": ["vitest.config.js", "vitest.config.ts", "vite.config.js", "vite.config.ts"],
        "cypress": ["cypress.config.js", "cypress.config.ts"],
        "playwright": ["playwright.config.js", "playwright.config.ts"],
        "mocha": ["mocha.opts", ".mocharc.json", ".mocharc.js"],
        "jasmine": ["jasmine.json", "spec/support/jasmine.json"]
    }

    # Check package.json dependencies
    if package_json.exists():
        try:
            pkg_data = json.loads(package_json.read_text())
            all_deps = {
                **pkg_data.get("dependencies", {}),
                **pkg_data.get("devDependencies", {})
            }

            for framework in frameworks:
                if framework in all_deps or f"@types/{framework}" in all_deps:
                    frameworks[framework] = True

            # Special cases
            if "@testing-library/react" in all_deps:
                frameworks["testing_library"] = True
            if "supertest" in all_deps:
                frameworks["supertest"] = True

        except Exception:
            pass

    # Check config files
    for framework, configs in config_files.items():
        for config in configs:
            if (path / config).exists():
                frameworks[framework] = True

    # Detect from test files
    test_files = _find_test_files(path)
    for test_file in test_files[:5]:  # Check first 5 test files
        try:
            content = test_file.read_text(encoding='utf-8')

            if 'describe(' in content and 'it(' in content:
                frameworks["jest"] = True
            if 'test(' in content:
                frameworks["jest"] = True
            if 'cy.' in content:
                frameworks["cypress"] = True
            if 'await page.' in content or 'await browser.' in content:
                frameworks["playwright"] = True
            if 'expect(' in content:
                frameworks["expect"] = True

        except Exception:
            continue

    return frameworks


def _find_test_files(path: Path) -> List[Path]:
    """Find all test files in the project."""
    test_patterns = [
        "**/*.test.{js,jsx,ts,tsx}",
        "**/*.spec.{js,jsx,ts,tsx}",
        "**/tests/**/*.{js,jsx,ts,tsx}",
        "**/test/**/*.{js,jsx,ts,tsx}",
        "**/__tests__/**/*.{js,jsx,ts,tsx}",
        "**/cypress/**/*.{js,ts}",
        "**/e2e/**/*.{js,ts}"
    ]

    test_files = []
    for pattern in test_patterns:
        test_files.extend(path.glob(pattern))

    # Remove duplicates
    return list(set(test_files))


def _is_test_file(file_path: Path) -> bool:
    """Check if a file is a test file."""
    test_indicators = [
        ".test.",
        ".spec.",
        "/tests/",
        "/test/",
        "/__tests__/",
        "/cypress/",
        "/e2e/"
    ]

    file_str = str(file_path)
    return any(indicator in file_str for indicator in test_indicators)


def _analyze_test_structure(test_files: List[Path]) -> Dict[str, Any]:
    """Analyze the structure and patterns of test files."""
    structure = {
        "unit_tests": 0,
        "integration_tests": 0,
        "e2e_tests": 0,
        "total_test_functions": 0,
        "test_patterns": {
            "describe_blocks": 0,
            "it_blocks": 0,
            "test_blocks": 0,
            "before_hooks": 0,
            "after_hooks": 0
        }
    }

    for test_file in test_files:
        try:
            content = test_file.read_text(encoding='utf-8')

            # Categorize tests
            if any(indicator in str(test_file) for indicator in ["/e2e/", "/cypress/", "playwright"]):
                structure["e2e_tests"] += 1
            elif any(indicator in str(test_file) for indicator in ["/integration/", "api.test", "request.test"]):
                structure["integration_tests"] += 1
            else:
                structure["unit_tests"] += 1

            # Count test patterns
            structure["test_patterns"]["describe_blocks"] += len(re.findall(r'describe\s*\(', content))
            structure["test_patterns"]["it_blocks"] += len(re.findall(r'it\s*\(', content))
            structure["test_patterns"]["test_blocks"] += len(re.findall(r'test\s*\(', content))
            structure["test_patterns"]["before_hooks"] += len(re.findall(r'before(?:Each|All)?\s*\(', content))
            structure["test_patterns"]["after_hooks"] += len(re.findall(r'after(?:Each|All)?\s*\(', content))

            # Total test functions
            structure["total_test_functions"] += (
                structure["test_patterns"]["it_blocks"] +
                structure["test_patterns"]["test_blocks"]
            )

        except Exception:
            continue

    return structure


async def _try_get_coverage_report(path: Path) -> Optional[Dict[str, Any]]:
    """Try to get test coverage report."""
    coverage_files = [
        path / "coverage" / "coverage-summary.json",
        path / "coverage" / "lcov-report" / "index.html",
        path / "coverage.json"
    ]

    # Try to read existing coverage report
    for coverage_file in coverage_files:
        if coverage_file.exists() and coverage_file.suffix == '.json':
            try:
                coverage_data = json.loads(coverage_file.read_text())
                if 'total' in coverage_data:
                    total = coverage_data['total']
                    return {
                        "lines": total.get('lines', {}).get('pct', 0),
                        "statements": total.get('statements', {}).get('pct', 0),
                        "functions": total.get('functions', {}).get('pct', 0),
                        "branches": total.get('branches', {}).get('pct', 0)
                    }
            except Exception:
                continue

    # Try to run coverage command
    try:
        result = subprocess.run(
            ['npm', 'run', 'test:coverage'],
            cwd=str(path),
            capture_output=True,
            text=True,
            timeout=60
        )

        # Parse coverage output (basic parsing)
        if result.stdout and 'All files' in result.stdout:
            # Look for coverage percentages in output
            lines = result.stdout.split('\n')
            for line in lines:
                if 'All files' in line:
                    # Extract percentages using regex
                    percentages = re.findall(r'(\d+(?:\.\d+)?)%', line)
                    if len(percentages) >= 4:
                        return {
                            "statements": float(percentages[0]),
                            "branches": float(percentages[1]),
                            "functions": float(percentages[2]),
                            "lines": float(percentages[3])
                        }

    except Exception:
        pass

    return None


def _analyze_testability(source_files: List[Path]) -> Dict[str, Any]:
    """Analyze source files for testability."""
    testability = {
        "testable_functions": 0,
        "untestable_patterns": [],
        "complexity_issues": 0,
        "dependency_issues": 0
    }

    for file in source_files:
        try:
            content = file.read_text(encoding='utf-8')

            # Count exportable functions
            exportable = len(re.findall(r'export\s+(?:function|const)\s+\w+', content))
            testability["testable_functions"] += exportable

            # Identify untestable patterns
            if 'window.' in content or 'document.' in content:
                testability["untestable_patterns"].append(f"{file.name}: DOM dependencies")

            if 'console.' in content:
                testability["untestable_patterns"].append(f"{file.name}: Console usage")

            # Complexity issues (functions longer than 50 lines)
            functions = re.findall(r'function\s+\w+\s*\([^)]*\)\s*\{', content)
            for func in functions:
                # Simplified complexity check
                func_start = content.find(func)
                if func_start != -1:
                    remaining_content = content[func_start:]
                    lines_count = remaining_content[:1000].count('\n')  # Check first 1000 chars
                    if lines_count > 50:
                        testability["complexity_issues"] += 1

            # Dependency issues (hard-coded imports)
            if "require('./config')" in content or "import './side-effects'" in content:
                testability["dependency_issues"] += 1

        except Exception:
            continue

    return testability


async def _generate_test_stubs_for_file(content: str, file_path: str, framework: str) -> Dict[str, Any]:
    """Generate test stubs for a specific file."""

    # Extract functions and classes to test
    functions = _extract_testable_functions(content)
    classes = _extract_testable_classes(content)

    # Generate test stubs based on framework
    stubs = {
        "framework": framework,
        "functions": [],
        "classes": [],
        "imports": _generate_test_imports(framework, file_path),
        "setup": _generate_test_setup(framework)
    }

    # Generate function tests
    for func in functions:
        test_stub = _generate_function_test_stub(func, framework)
        stubs["functions"].append(test_stub)

    # Generate class tests
    for cls in classes:
        test_stub = _generate_class_test_stub(cls, framework)
        stubs["classes"].append(test_stub)

    return stubs


def _extract_testable_functions(content: str) -> List[Dict[str, Any]]:
    """Extract functions that can be tested."""
    functions = []

    # Function declarations
    func_pattern = r'export\s+(?:async\s+)?function\s+(\w+)\s*\(([^)]*)\)(?:\s*:\s*([^{]+))?\s*\{'
    for match in re.finditer(func_pattern, content):
        functions.append({
            "name": match.group(1),
            "params": match.group(2).strip() if match.group(2) else "",
            "return_type": match.group(3).strip() if match.group(3) else "unknown",
            "is_async": "async" in match.group(0)
        })

    # Const arrow functions
    arrow_pattern = r'export\s+const\s+(\w+)\s*(?::\s*[^=]+)?\s*=\s*(?:async\s+)?\(([^)]*)\)(?:\s*:\s*([^=]+))?\s*=>'
    for match in re.finditer(arrow_pattern, content):
        functions.append({
            "name": match.group(1),
            "params": match.group(2).strip() if match.group(2) else "",
            "return_type": match.group(3).strip() if match.group(3) else "unknown",
            "is_async": "async" in match.group(0)
        })

    return functions


def _extract_testable_classes(content: str) -> List[Dict[str, Any]]:
    """Extract classes that can be tested."""
    classes = []

    class_pattern = r'export\s+class\s+(\w+)(?:\s+extends\s+(\w+))?\s*\{'
    for match in re.finditer(class_pattern, content):
        # Extract methods (simplified)
        class_name = match.group(1)
        class_start = match.end()

        # Find class end (simplified - just look for methods)
        class_content = content[class_start:class_start + 1000]  # Limit search
        methods = re.findall(r'(?:public\s+|private\s+|protected\s+)?(\w+)\s*\([^)]*\)\s*[:{]', class_content)

        classes.append({
            "name": class_name,
            "extends": match.group(2) if match.group(2) else None,
            "methods": methods[:5]  # Limit to first 5 methods
        })

    return classes


def _generate_test_imports(framework: str, file_path: str) -> List[str]:
    """Generate appropriate imports for the test framework."""
    file_name = Path(file_path).stem
    imports = []

    if framework == "jest":
        imports = [
            f"import {{ {file_name} }} from './{file_name}';",
            "import { describe, it, expect, beforeEach, afterEach } from '@jest/globals';"
        ]
    elif framework == "vitest":
        imports = [
            f"import {{ {file_name} }} from './{file_name}';",
            "import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';"
        ]
    elif framework == "cypress":
        imports = [
            "/// <reference types=\"cypress\" />"
        ]
    elif framework == "playwright":
        imports = [
            "import { test, expect } from '@playwright/test';"
        ]

    return imports


def _generate_test_setup(framework: str) -> List[str]:
    """Generate test setup code for the framework."""
    setup = []

    if framework in ["jest", "vitest"]:
        setup = [
            "describe('Component Name', () => {",
            "  beforeEach(() => {",
            "    // Setup before each test",
            "  });",
            "",
            "  afterEach(() => {",
            "    // Cleanup after each test",
            "  });"
        ]
    elif framework == "cypress":
        setup = [
            "describe('E2E Test Suite', () => {",
            "  beforeEach(() => {",
            "    cy.visit('/');",
            "  });"
        ]
    elif framework == "playwright":
        setup = [
            "test.describe('Page Tests', () => {",
            "  test.beforeEach(async ({ page }) => {",
            "    await page.goto('/');",
            "  });"
        ]

    return setup


def _generate_function_test_stub(func: Dict[str, Any], framework: str) -> Dict[str, Any]:
    """Generate test stub for a function."""
    name = func["name"]
    params = func["params"]
    is_async = func["is_async"]

    if framework in ["jest", "vitest"]:
        test_code = [
            f"  it('should test {name}', {'async ' if is_async else ''}() => {{",
            f"    // Arrange",
            f"    const input = /* test input */;",
            f"    const expected = /* expected output */;",
            f"",
            f"    // Act",
            f"    const result = {'await ' if is_async else ''}{name}(input);",
            f"",
            f"    // Assert",
            f"    expect(result).toBe(expected);",
            f"  }});"
        ]
    elif framework == "cypress":
        test_code = [
            f"  it('should test {name}', () => {{",
            f"    cy.window().then((win) => {{",
            f"      // Call function through window object or page interaction",
            f"      // cy.get('[data-testid=\"button\"]').click();",
            f"    }});",
            f"  }});"
        ]
    else:
        test_code = [
            f"  test('{name} should work correctly', async ({{ page }}) => {{",
            f"    // Interact with page elements",
            f"    // await page.click('[data-testid=\"button\"]');",
            f"  }});"
        ]

    return {
        "function_name": name,
        "code": test_code
    }


def _generate_class_test_stub(cls: Dict[str, Any], framework: str) -> Dict[str, Any]:
    """Generate test stub for a class."""
    name = cls["name"]
    methods = cls.get("methods", [])

    if framework in ["jest", "vitest"]:
        test_code = [
            f"  describe('{name}', () => {{",
            f"    let instance: {name};",
            f"",
            f"    beforeEach(() => {{",
            f"      instance = new {name}();",
            f"    }});",
            f""
        ]

        for method in methods:
            test_code.extend([
                f"    it('should test {method}', () => {{",
                f"      // Test {method} method",
                f"      const result = instance.{method}();",
                f"      expect(result).toBeDefined();",
                f"    }});",
                f""
            ])

        test_code.append("  });")
    else:
        test_code = [
            f"  // Class {name} testing would be done through page interactions",
            f"  // in {framework} framework"
        ]

    return {
        "class_name": name,
        "code": test_code
    }


async def _analyze_test_patterns(content: str, file_path: str, test_type: str) -> List[Dict[str, Any]]:
    """Analyze code for appropriate testing patterns."""
    suggestions = []

    # Analyze based on test type
    if test_type == "unit":
        suggestions.extend(_analyze_unit_test_patterns(content))
    elif test_type == "integration":
        suggestions.extend(_analyze_integration_test_patterns(content))
    elif test_type == "e2e":
        suggestions.extend(_analyze_e2e_test_patterns(content))

    # General testing patterns
    suggestions.extend(_analyze_general_test_patterns(content))

    return suggestions


def _analyze_unit_test_patterns(content: str) -> List[Dict[str, Any]]:
    """Analyze unit testing patterns."""
    suggestions = []

    # Check for pure functions
    pure_functions = len(re.findall(r'export\s+(?:const|function)\s+\w+\s*=?\s*\([^)]*\)\s*(?::\s*[^{]+)?\s*(?:=>|\{)', content))
    if pure_functions > 0:
        suggestions.append({
            "type": "unit_testing",
            "priority": "high",
            "message": f"Found {pure_functions} exportable functions suitable for unit testing",
            "pattern": "Pure Function Testing",
            "example": "test('should return expected result', () => { expect(myFunction(input)).toBe(expected); });"
        })

    # Check for classes
    classes = len(re.findall(r'export\s+class\s+\w+', content))
    if classes > 0:
        suggestions.append({
            "type": "unit_testing",
            "priority": "high",
            "message": f"Found {classes} classes that need unit tests",
            "pattern": "Class Testing",
            "example": "describe('MyClass', () => { let instance; beforeEach(() => { instance = new MyClass(); }); });"
        })

    # Check for async functions
    async_functions = len(re.findall(r'async\s+(?:function|\w+\s*=>)', content))
    if async_functions > 0:
        suggestions.append({
            "type": "async_testing",
            "priority": "medium",
            "message": f"Found {async_functions} async functions requiring async testing patterns",
            "pattern": "Async Testing",
            "example": "test('async function', async () => { const result = await myAsyncFunction(); });"
        })

    return suggestions


def _analyze_integration_test_patterns(content: str) -> List[Dict[str, Any]]:
    """Analyze integration testing patterns."""
    suggestions = []

    # Check for API endpoints
    api_patterns = len(re.findall(r'app\.(get|post|put|delete)', content))
    if api_patterns > 0:
        suggestions.append({
            "type": "api_testing",
            "priority": "high",
            "message": f"Found {api_patterns} API endpoints for integration testing",
            "pattern": "API Testing",
            "example": "test('API endpoint', async () => { const response = await request(app).get('/api/endpoint'); });"
        })

    # Check for database operations
    db_operations = len(re.findall(r'(?:findOne|findMany|create|update|delete|save)\s*\(', content))
    if db_operations > 0:
        suggestions.append({
            "type": "database_testing",
            "priority": "high",
            "message": f"Found {db_operations} database operations for integration testing",
            "pattern": "Database Testing",
            "example": "test('database operation', async () => { const user = await User.create(data); expect(user.id).toBeDefined(); });"
        })

    return suggestions


def _analyze_e2e_test_patterns(content: str) -> List[Dict[str, Any]]:
    """Analyze E2E testing patterns."""
    suggestions = []

    # Check for React components
    react_components = len(re.findall(r'export\s+(?:default\s+)?(?:function|const)\s+\w+.*return\s*\(?\s*<', content))
    if react_components > 0:
        suggestions.append({
            "type": "component_testing",
            "priority": "medium",
            "message": f"Found {react_components} React components for E2E testing",
            "pattern": "Component E2E Testing",
            "example": "test('component interaction', async ({ page }) => { await page.click('[data-testid=\"button\"]'); });"
        })

    # Check for form elements
    form_elements = len(re.findall(r'<(?:form|input|button|select)', content))
    if form_elements > 0:
        suggestions.append({
            "type": "form_testing",
            "priority": "high",
            "message": f"Found {form_elements} form elements for E2E testing",
            "pattern": "Form Testing",
            "example": "test('form submission', async ({ page }) => { await page.fill('input[name=\"email\"]', 'test@example.com'); });"
        })

    return suggestions


def _analyze_general_test_patterns(content: str) -> List[Dict[str, Any]]:
    """Analyze general testing patterns."""
    suggestions = []

    # Check for error handling
    try_catch = len(re.findall(r'try\s*\{', content))
    if try_catch > 0:
        suggestions.append({
            "type": "error_testing",
            "priority": "medium",
            "message": f"Found {try_catch} error handling blocks - consider testing error scenarios",
            "pattern": "Error Testing",
            "example": "test('should handle errors', () => { expect(() => riskyFunction()).toThrow(); });"
        })

    # Check for conditional logic
    conditionals = len(re.findall(r'if\s*\(', content))
    if conditionals > 5:
        suggestions.append({
            "type": "branch_testing",
            "priority": "medium",
            "message": f"Found {conditionals} conditional statements - ensure all branches are tested",
            "pattern": "Branch Testing",
            "example": "// Test both true and false conditions for each if statement"
        })

    return suggestions


def _generate_testing_recommendations(frameworks: Dict[str, bool], test_count: int,
                                    source_count: int, coverage: Optional[Dict]) -> List[Dict[str, Any]]:
    """Generate testing recommendations based on project analysis."""
    recommendations = []

    # Framework recommendations
    active_frameworks = [f for f, active in frameworks.items() if active]
    if not active_frameworks:
        recommendations.append({
            "type": "framework_setup",
            "priority": "high",
            "message": "No testing framework detected",
            "suggestion": "Set up Jest or Vitest for unit testing",
            "benefit": "Enables automated testing and code quality assurance"
        })

    # Test coverage recommendations
    if test_count == 0 and source_count > 0:
        recommendations.append({
            "type": "test_coverage",
            "priority": "high",
            "message": "No test files found",
            "suggestion": "Create test files for your source code",
            "benefit": "Catch bugs early and ensure code reliability"
        })
    elif test_count < source_count * 0.5:
        recommendations.append({
            "type": "test_coverage",
            "priority": "medium",
            "message": f"Low test coverage: {test_count} tests for {source_count} source files",
            "suggestion": "Aim for at least one test file per source file",
            "benefit": "Better test coverage catches more potential issues"
        })

    # Coverage percentage recommendations
    if coverage:
        low_coverage_areas = []
        for metric, value in coverage.items():
            if value < 70:
                low_coverage_areas.append(f"{metric}: {value}%")

        if low_coverage_areas:
            recommendations.append({
                "type": "coverage_improvement",
                "priority": "medium",
                "message": f"Low coverage in: {', '.join(low_coverage_areas)}",
                "suggestion": "Add tests to improve coverage in these areas",
                "benefit": "Higher coverage reduces bugs in production"
            })

    # Framework-specific recommendations
    if frameworks.get("jest") and not frameworks.get("testing_library"):
        recommendations.append({
            "type": "testing_tools",
            "priority": "low",
            "message": "Consider adding React Testing Library for component testing",
            "suggestion": "npm install @testing-library/react @testing-library/jest-dom",
            "benefit": "Better component testing utilities and best practices"
        })

    return recommendations


def _format_test_coverage_results(analysis: Dict[str, Any]) -> str:
    """Format test coverage analysis results."""
    output = []

    output.append("🧪 **Test Coverage Analysis**\n")

    # Frameworks
    frameworks = analysis.get("frameworks", {})
    active_frameworks = [f for f, active in frameworks.items() if active]

    if active_frameworks:
        output.append("🔧 **Testing Frameworks:**")
        for framework in active_frameworks:
            output.append(f"- {framework.title()}: ✅")
        output.append("")
    else:
        output.append("❌ **No testing frameworks detected**\n")

    # Test files
    test_files = analysis.get("test_files", {})
    test_count = test_files.get("count", 0)
    output.append(f"📄 **Test Files:** {test_count}")
    if test_count > 0:
        files_list = test_files.get("files", [])
        for file in files_list[:5]:  # Show first 5 files
            output.append(f"  - {file}")
        if len(files_list) > 5:
            output.append(f"  - ... and {len(files_list) - 5} more")
    output.append("")

    # Test structure
    structure = analysis.get("test_structure", {})
    if structure.get("total_test_functions", 0) > 0:
        output.append("📊 **Test Structure:**")
        output.append(f"- Unit tests: {structure.get('unit_tests', 0)}")
        output.append(f"- Integration tests: {structure.get('integration_tests', 0)}")
        output.append(f"- E2E tests: {structure.get('e2e_tests', 0)}")
        output.append(f"- Total test functions: {structure.get('total_test_functions', 0)}")
        output.append("")

    # Coverage
    coverage = analysis.get("coverage")
    if coverage:
        output.append("📈 **Coverage Report:**")
        for metric, value in coverage.items():
            emoji = "✅" if value >= 80 else "🟡" if value >= 60 else "❌"
            output.append(f"{emoji} {metric.title()}: {value}%")
        output.append("")
    else:
        output.append("⚠️ **Coverage report not available**\n")

    # Testability
    testability = analysis.get("testability", {})
    if testability:
        output.append("🔍 **Code Testability:**")
        output.append(f"- Testable functions: {testability.get('testable_functions', 0)}")
        output.append(f"- Complexity issues: {testability.get('complexity_issues', 0)}")
        output.append(f"- Dependency issues: {testability.get('dependency_issues', 0)}")

        untestable = testability.get("untestable_patterns", [])
        if untestable:
            output.append("⚠️ Untestable patterns:")
            for pattern in untestable[:3]:
                output.append(f"  - {pattern}")
        output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")
            if rec.get("suggestion"):
                output.append(f"   💡 {rec['suggestion']}")
            if rec.get("benefit"):
                output.append(f"   ✅ {rec['benefit']}")
        output.append("")

    return '\n'.join(output)


def _format_test_stubs(stubs: Dict[str, Any], framework: str) -> str:
    """Format generated test stubs."""
    output = []

    output.append(f"🧪 **Generated Test Stubs ({framework.title()})**\n")

    # Imports
    imports = stubs.get("imports", [])
    if imports:
        output.append("📦 **Imports:**")
        for imp in imports:
            output.append(f"```typescript\n{imp}\n```")
        output.append("")

    # Setup
    setup = stubs.get("setup", [])
    if setup:
        output.append("⚙️ **Test Setup:**")
        output.append("```typescript")
        output.extend(setup)
        output.append("```")
        output.append("")

    # Function tests
    functions = stubs.get("functions", [])
    if functions:
        output.append("🔧 **Function Tests:**")
        for func in functions:
            output.append(f"```typescript")
            output.extend(func["code"])
            output.append("```")
        output.append("")

    # Class tests
    classes = stubs.get("classes", [])
    if classes:
        output.append("🏗️ **Class Tests:**")
        for cls in classes:
            output.append("```typescript")
            output.extend(cls["code"])
            output.append("```")
        output.append("")

    output.append("💡 **Next Steps:**")
    output.append("1. Replace placeholder values with actual test data")
    output.append("2. Add more test cases for edge cases")
    output.append("3. Set up test environment and mocks if needed")
    output.append("4. Run tests and verify they pass")

    return '\n'.join(output)


def _format_test_pattern_suggestions(suggestions: List[Dict[str, Any]], test_type: str) -> str:
    """Format test pattern suggestions."""
    output = []

    output.append(f"💡 **Testing Pattern Suggestions ({test_type.title()})**\n")

    if not suggestions:
        output.append("✅ No specific testing patterns identified")
        return '\n'.join(output)

    # Group by type
    by_type = {}
    for suggestion in suggestions:
        stype = suggestion.get("type", "general")
        if stype not in by_type:
            by_type[stype] = []
        by_type[stype].append(suggestion)

    for suggestion_type, items in by_type.items():
        type_name = suggestion_type.replace('_', ' ').title()
        output.append(f"📝 **{type_name}:**")

        for item in items:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(item.get("priority"), "⚪")
            message = item.get("message", "")
            pattern = item.get("pattern", "")
            example = item.get("example", "")

            output.append(f"{priority_emoji} {message}")
            if pattern:
                output.append(f"   📋 Pattern: {pattern}")
            if example:
                output.append(f"   💻 Example: `{example}`")
            output.append("")

    return '\n'.join(output)