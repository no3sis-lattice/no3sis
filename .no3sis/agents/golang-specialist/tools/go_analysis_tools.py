"""
Go Code Analysis Tools

Core analysis tools for Go language patterns, conventions, and code quality.
Provides comprehensive static analysis capabilities for Go codebases.
"""

import ast
import os
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple


def analyze_go_code(file_path: str, analysis_type: str, config: Dict[str, Any]) -> str:
    """
    Analyze Go source code for patterns, idioms, and potential issues.

    Args:
        file_path: Path to the Go file to analyze
        analysis_type: Type of analysis (basic, comprehensive, performance)
        config: Agent configuration

    Returns:
        Detailed analysis report
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        analysis = {
            "file_path": file_path,
            "analysis_type": analysis_type,
            "file_size": len(content),
            "line_count": len(content.splitlines()),
        }

        # Basic analysis
        analysis.update(_analyze_basic_structure(content, config))

        if analysis_type in ["comprehensive", "performance"]:
            analysis.update(_analyze_functions(content, config))
            analysis.update(_analyze_types(content, config))
            analysis.update(_analyze_imports(content, config))

        if analysis_type == "performance":
            analysis.update(_analyze_performance_patterns(content, config))

        return _format_analysis_report(analysis, config)

    except Exception as e:
        return f"❌ Analysis failed: {str(e)}"


def check_go_conventions(file_path: str, strict_mode: bool, config: Dict[str, Any]) -> str:
    """
    Check Go code against standard conventions and style guidelines.

    Args:
        file_path: Path to the Go file to check
        strict_mode: Whether to apply strict convention checking
        config: Agent configuration

    Returns:
        Convention compliance report
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        violations = []

        # Check naming conventions
        violations.extend(_check_naming_conventions(content, strict_mode, config))

        # Check formatting
        violations.extend(_check_formatting(file_path, config))

        # Check comments and documentation
        violations.extend(_check_documentation(content, config))

        # Check function complexity
        violations.extend(_check_function_complexity(content, config))

        if not violations:
            return "✅ All Go conventions are properly followed!"

        report = "## Go Convention Violations\n\n"

        for violation in violations:
            severity = violation.get('severity', 'info')
            icon = {'error': '❌', 'warning': '⚠️', 'info': '💡'}.get(severity, '💡')
            report += f"{icon} **{violation['type']}** (Line {violation.get('line', '?')})\n"
            report += f"   {violation['message']}\n"
            if 'suggestion' in violation:
                report += f"   💡 Suggestion: {violation['suggestion']}\n"
            report += "\n"

        return report

    except Exception as e:
        return f"❌ Convention check failed: {str(e)}"


def suggest_improvements(file_path: str, focus_area: str, config: Dict[str, Any]) -> str:
    """
    Suggest improvements for Go code quality and performance.

    Args:
        file_path: Path to the Go file to analyze
        focus_area: Area to focus on (performance, readability, idiomatic, all)
        config: Agent configuration

    Returns:
        Improvement suggestions with code examples
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        suggestions = []

        if focus_area in ["performance", "all"]:
            suggestions.extend(_suggest_performance_improvements(content, config))

        if focus_area in ["readability", "all"]:
            suggestions.extend(_suggest_readability_improvements(content, config))

        if focus_area in ["idiomatic", "all"]:
            suggestions.extend(_suggest_idiomatic_improvements(content, config))

        if not suggestions:
            return f"✅ No improvements suggested for focus area: {focus_area}"

        report = f"## Go Code Improvements - {focus_area.title()}\n\n"

        for i, suggestion in enumerate(suggestions, 1):
            report += f"### {i}. {suggestion['title']}\n"
            report += f"**Priority:** {suggestion['priority']}\n"
            report += f"**Impact:** {suggestion['impact']}\n\n"
            report += f"{suggestion['description']}\n\n"

            if 'before' in suggestion:
                report += "**Before:**\n```go\n"
                report += suggestion['before']
                report += "\n```\n\n"

            if 'after' in suggestion:
                report += "**After:**\n```go\n"
                report += suggestion['after']
                report += "\n```\n\n"

        return report

    except Exception as e:
        return f"❌ Improvement analysis failed: {str(e)}"


def _analyze_basic_structure(content: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze basic Go file structure."""
    analysis = {}

    # Package declaration
    package_match = re.search(r'^package\s+(\w+)', content, re.MULTILINE)
    analysis['package'] = package_match.group(1) if package_match else "unknown"

    # Count different elements
    analysis['import_count'] = len(re.findall(r'^import\s+["\(]', content, re.MULTILINE))
    analysis['function_count'] = len(re.findall(r'^func\s+', content, re.MULTILINE))
    analysis['struct_count'] = len(re.findall(r'^type\s+\w+\s+struct', content, re.MULTILINE))
    analysis['interface_count'] = len(re.findall(r'^type\s+\w+\s+interface', content, re.MULTILINE))

    # Check for main function
    analysis['has_main'] = bool(re.search(r'^func\s+main\s*\(\s*\)', content, re.MULTILINE))

    return analysis


def _analyze_functions(content: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze function patterns and complexity."""
    functions = []

    # Find all function definitions
    func_pattern = r'^func\s+(?:\([^)]*\)\s+)?(\w+)\s*\([^)]*\)(?:\s*\([^)]*\))?\s*\{'
    matches = re.finditer(func_pattern, content, re.MULTILINE)

    for match in matches:
        func_name = match.group(1)
        func_start = match.start()

        # Count lines in function (rough approximation)
        func_content = content[func_start:]
        brace_count = 0
        func_end = func_start

        for i, char in enumerate(func_content):
            if char == '{':
                brace_count += 1
            elif char == '}':
                brace_count -= 1
                if brace_count == 0:
                    func_end = func_start + i
                    break

        func_body = content[func_start:func_end]
        line_count = len(func_body.splitlines())

        functions.append({
            'name': func_name,
            'line_count': line_count,
            'complexity': _calculate_cyclomatic_complexity(func_body)
        })

    return {'functions': functions}


def _analyze_types(content: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze type definitions and usage."""
    types = []

    # Find struct definitions
    struct_pattern = r'^type\s+(\w+)\s+struct\s*\{'
    struct_matches = re.finditer(struct_pattern, content, re.MULTILINE)

    for match in struct_matches:
        type_name = match.group(1)
        types.append({
            'name': type_name,
            'kind': 'struct',
            'exported': type_name[0].isupper()
        })

    # Find interface definitions
    interface_pattern = r'^type\s+(\w+)\s+interface\s*\{'
    interface_matches = re.finditer(interface_pattern, content, re.MULTILINE)

    for match in interface_matches:
        type_name = match.group(1)
        types.append({
            'name': type_name,
            'kind': 'interface',
            'exported': type_name[0].isupper()
        })

    return {'types': types}


def _analyze_imports(content: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze import statements and dependencies."""
    imports = []

    # Single line imports
    single_imports = re.findall(r'^import\s+"([^"]+)"', content, re.MULTILINE)
    imports.extend(single_imports)

    # Multi-line imports
    import_block = re.search(r'^import\s*\(\s*\n(.*?)\n\s*\)', content, re.MULTILINE | re.DOTALL)
    if import_block:
        import_lines = import_block.group(1).strip().split('\n')
        for line in import_lines:
            line = line.strip()
            if line and not line.startswith('//'):
                # Extract import path from line like: "fmt" or alias "path"
                match = re.search(r'"([^"]+)"', line)
                if match:
                    imports.append(match.group(1))

    # Categorize imports
    stdlib_imports = []
    third_party_imports = []

    for imp in imports:
        if '.' not in imp or imp.startswith('golang.org/x/'):
            stdlib_imports.append(imp)
        else:
            third_party_imports.append(imp)

    return {
        'imports': {
            'total': len(imports),
            'stdlib': stdlib_imports,
            'third_party': third_party_imports
        }
    }


def _analyze_performance_patterns(content: str, config: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze performance-related patterns."""
    patterns = []

    # String concatenation in loops
    if re.search(r'for.*\{.*\+.*string.*\}', content, re.DOTALL):
        patterns.append({
            'type': 'string_concatenation_in_loop',
            'severity': 'warning',
            'message': 'String concatenation in loop detected - consider using strings.Builder'
        })

    # Slice append in loop without pre-allocation
    if re.search(r'for.*\{.*append\(.*\).*\}', content, re.DOTALL):
        patterns.append({
            'type': 'slice_append_in_loop',
            'severity': 'info',
            'message': 'Slice append in loop - consider pre-allocating capacity'
        })

    return {'performance_patterns': patterns}


def _check_naming_conventions(content: str, strict_mode: bool, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check Go naming conventions."""
    violations = []
    lines = content.splitlines()

    for i, line in enumerate(lines, 1):
        # Check for non-Go naming patterns
        if re.search(r'(var|func|type)\s+[a-z]+_[a-zA-Z]', line):
            violations.append({
                'type': 'naming_convention',
                'severity': 'warning',
                'line': i,
                'message': 'Use camelCase instead of snake_case for Go identifiers',
                'suggestion': 'Convert to camelCase (e.g., userName instead of user_name)'
            })

    return violations


def _check_formatting(file_path: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check Go formatting using gofmt."""
    violations = []

    try:
        # Run gofmt to check formatting
        result = subprocess.run(['gofmt', '-d', file_path],
                              capture_output=True, text=True, timeout=10)

        if result.stdout:
            violations.append({
                'type': 'formatting',
                'severity': 'warning',
                'message': 'File is not properly formatted',
                'suggestion': 'Run `gofmt -w filename.go` to fix formatting'
            })
    except (subprocess.TimeoutExpired, FileNotFoundError):
        # gofmt not available or timeout
        pass

    return violations


def _check_documentation(content: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check documentation completeness."""
    violations = []

    # Check for package documentation
    if not re.search(r'^//.*\npackage\s+\w+', content, re.MULTILINE):
        violations.append({
            'type': 'documentation',
            'severity': 'info',
            'line': 1,
            'message': 'Missing package documentation',
            'suggestion': 'Add a comment before package declaration describing the package purpose'
        })

    return violations


def _check_function_complexity(content: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check function complexity."""
    violations = []
    max_complexity = config.get('go', {}).get('conventions', {}).get('max_cognitive_complexity', 10)

    func_pattern = r'^func\s+(?:\([^)]*\)\s+)?(\w+)'
    matches = re.finditer(func_pattern, content, re.MULTILINE)

    for match in matches:
        func_name = match.group(1)
        func_start = match.start()

        # Get function body
        func_content = content[func_start:]
        complexity = _calculate_cyclomatic_complexity(func_content)

        if complexity > max_complexity:
            violations.append({
                'type': 'complexity',
                'severity': 'warning',
                'message': f'Function {func_name} has high complexity ({complexity})',
                'suggestion': f'Consider breaking down function (max: {max_complexity})'
            })

    return violations


def _calculate_cyclomatic_complexity(func_content: str) -> int:
    """Calculate cyclomatic complexity for a function."""
    complexity = 1  # Base complexity

    # Count decision points
    keywords = ['if', 'else if', 'switch', 'case', 'for', 'range', '&&', '||']

    for keyword in keywords:
        if keyword in ['&&', '||']:
            complexity += func_content.count(keyword)
        else:
            complexity += len(re.findall(r'\b' + keyword + r'\b', func_content))

    return complexity


def _suggest_performance_improvements(content: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Suggest performance improvements."""
    suggestions = []

    # String concatenation
    if '+' in content and 'string' in content:
        suggestions.append({
            'title': 'Use strings.Builder for string concatenation',
            'priority': 'medium',
            'impact': 'performance',
            'description': 'String concatenation with + operator creates new strings. Use strings.Builder for better performance.',
            'before': 'result := str1 + str2 + str3',
            'after': 'var builder strings.Builder\nbuilder.WriteString(str1)\nbuilder.WriteString(str2)\nbuilder.WriteString(str3)\nresult := builder.String()'
        })

    return suggestions


def _suggest_readability_improvements(content: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Suggest readability improvements."""
    suggestions = []

    # Error handling
    if 'if err != nil' in content:
        suggestions.append({
            'title': 'Consider error wrapping for better context',
            'priority': 'low',
            'impact': 'maintainability',
            'description': 'Wrap errors with context to improve debugging.',
            'before': 'if err != nil {\n    return err\n}',
            'after': 'if err != nil {\n    return fmt.Errorf("operation failed: %w", err)\n}'
        })

    return suggestions


def _suggest_idiomatic_improvements(content: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Suggest idiomatic Go improvements."""
    suggestions = []

    # Interface usage
    if 'interface{}' in content:
        suggestions.append({
            'title': 'Consider using specific interfaces instead of interface{}',
            'priority': 'medium',
            'impact': 'type_safety',
            'description': 'Use specific interfaces for better type safety and documentation.',
            'before': 'func process(data interface{}) error',
            'after': 'func process(data Processor) error\n\ntype Processor interface {\n    Process() error\n}'
        })

    return suggestions


def _format_analysis_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the analysis report."""
    report = f"# Go Code Analysis Report\n\n"
    report += f"**File:** `{analysis['file_path']}`\n"
    report += f"**Package:** `{analysis.get('package', 'unknown')}`\n"
    report += f"**Analysis Type:** {analysis['analysis_type']}\n\n"

    report += "## File Statistics\n"
    report += f"- Lines: {analysis['line_count']}\n"
    report += f"- Size: {analysis['file_size']} bytes\n"
    report += f"- Functions: {analysis['function_count']}\n"
    report += f"- Structs: {analysis['struct_count']}\n"
    report += f"- Interfaces: {analysis['interface_count']}\n"
    report += f"- Has main(): {'✅' if analysis.get('has_main') else '❌'}\n\n"

    if 'imports' in analysis:
        imports = analysis['imports']
        report += "## Imports\n"
        report += f"- Total: {imports['total']}\n"
        report += f"- Standard library: {len(imports['stdlib'])}\n"
        report += f"- Third party: {len(imports['third_party'])}\n\n"

    if 'functions' in analysis:
        report += "## Functions\n"
        for func in analysis['functions']:
            complexity_icon = "🔴" if func['complexity'] > 10 else "🟡" if func['complexity'] > 5 else "🟢"
            report += f"- `{func['name']}`: {func['line_count']} lines, complexity {func['complexity']} {complexity_icon}\n"
        report += "\n"

    return report