"""
Go Testing Tools

Specialized tools for Go testing patterns, coverage analysis, and test generation.
Focuses on table-driven tests, benchmarks, and Go testing best practices.
"""

import os
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple


def analyze_tests(test_path: str, coverage_check: bool, config: Dict[str, Any]) -> str:
    """
    Analyze Go test patterns and quality.

    Args:
        test_path: Path to test files or directory
        coverage_check: Whether to include coverage analysis
        config: Agent configuration

    Returns:
        Comprehensive test analysis report
    """
    try:
        if not os.path.exists(test_path):
            return f"❌ Path not found: {test_path}"

        analysis = {
            "path": test_path,
            "test_files": [],
            "test_functions": [],
            "benchmark_functions": [],
            "example_functions": [],
            "test_patterns": [],
            "issues": []
        }

        # Find test files
        test_files = _find_test_files(test_path)
        analysis["test_files"] = test_files

        # Analyze each test file
        for test_file in test_files:
            with open(test_file, 'r', encoding='utf-8') as f:
                content = f.read()

            # Find test functions
            test_funcs = _find_test_functions(content, test_file)
            analysis["test_functions"].extend(test_funcs)

            # Find benchmark functions
            bench_funcs = _find_benchmark_functions(content, test_file)
            analysis["benchmark_functions"].extend(bench_funcs)

            # Find example functions
            example_funcs = _find_example_functions(content, test_file)
            analysis["example_functions"].extend(example_funcs)

            # Analyze test patterns
            patterns = _analyze_test_patterns(content, test_file, config)
            analysis["test_patterns"].extend(patterns)

            # Check for issues
            issues = _check_test_issues(content, test_file, config)
            analysis["issues"].extend(issues)

        # Run coverage analysis if requested
        if coverage_check:
            coverage_data = _run_coverage_analysis(test_path, config)
            analysis["coverage"] = coverage_data

        return _format_test_analysis_report(analysis, config)

    except Exception as e:
        return f"❌ Test analysis failed: {str(e)}"


def generate_table_tests(function_name: str, file_path: str, config: Dict[str, Any]) -> str:
    """
    Generate table-driven tests for a Go function.

    Args:
        function_name: Name of the function to test
        file_path: Path to the file containing the function
        config: Agent configuration

    Returns:
        Generated table-driven test code
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # Find the function definition
        function_def = _find_function_definition(content, function_name)
        if not function_def:
            return f"❌ Function '{function_name}' not found in {file_path}"

        # Parse function signature
        signature = _parse_function_signature(function_def)
        if not signature:
            return f"❌ Could not parse function signature for '{function_name}'"

        # Generate test code
        test_code = _generate_table_test_code(function_name, signature, config)

        return f"# Generated Table-Driven Test for `{function_name}`\n\n```go\n{test_code}\n```\n\n" + \
               "**Usage Instructions:**\n" + \
               "1. Copy this code to your `*_test.go` file\n" + \
               "2. Fill in the test cases with appropriate input/output values\n" + \
               "3. Run with `go test`\n"

    except Exception as e:
        return f"❌ Table test generation failed: {str(e)}"


def check_test_coverage(package_path: str, threshold: float, config: Dict[str, Any]) -> str:
    """
    Check test coverage for Go packages.

    Args:
        package_path: Path to the Go package
        threshold: Minimum coverage threshold
        config: Agent configuration

    Returns:
        Detailed coverage analysis report
    """
    try:
        if not os.path.exists(package_path):
            return f"❌ Package path not found: {package_path}"

        coverage_analysis = {
            "package_path": package_path,
            "threshold": threshold,
            "coverage_data": None,
            "files_coverage": [],
            "functions_coverage": [],
            "uncovered_lines": [],
            "recommendations": []
        }

        # Run coverage analysis
        coverage_result = _run_detailed_coverage(package_path, config)
        if coverage_result:
            coverage_analysis["coverage_data"] = coverage_result

            # Parse coverage details
            if "files" in coverage_result:
                coverage_analysis["files_coverage"] = coverage_result["files"]
            
            if "functions" in coverage_result:
                coverage_analysis["functions_coverage"] = coverage_result["functions"]
            
            if "uncovered" in coverage_result:
                coverage_analysis["uncovered_lines"] = coverage_result["uncovered"]

            # Generate recommendations
            recommendations = _generate_coverage_recommendations(
                coverage_result, threshold, config
            )
            coverage_analysis["recommendations"] = recommendations

        return _format_coverage_report(coverage_analysis, config)

    except Exception as e:
        return f"❌ Coverage analysis failed: {str(e)}"


def _find_test_files(path: str) -> List[str]:
    """Find all test files in the given path."""
    test_files = []
    
    if os.path.isfile(path):
        if path.endswith('_test.go'):
            test_files.append(path)
    else:
        # Directory - find all test files
        path_obj = Path(path)
        for test_file in path_obj.rglob('*_test.go'):
            test_files.append(str(test_file))
    
    return test_files


def _find_test_functions(content: str, file_path: str) -> List[Dict[str, Any]]:
    """Find all test functions in the content."""
    functions = []
    
    # Pattern for test functions: func TestXxx(*testing.T)
    test_pattern = r'^func\s+(Test\w+)\s*\(\s*\w+\s+\*testing\.T\s*\)\s*\{'
    matches = re.finditer(test_pattern, content, re.MULTILINE)
    
    for match in matches:
        func_name = match.group(1)
        line_num = content[:match.start()].count('\n') + 1
        
        # Get function body to analyze complexity
        func_body = _extract_function_body(content, match.start())
        
        functions.append({
            "name": func_name,
            "line": line_num,
            "file": file_path,
            "type": "test",
            "complexity": _calculate_test_complexity(func_body),
            "has_subtests": 't.Run(' in func_body
        })
    
    return functions


def _find_benchmark_functions(content: str, file_path: str) -> List[Dict[str, Any]]:
    """Find all benchmark functions in the content."""
    functions = []
    
    # Pattern for benchmark functions: func BenchmarkXxx(*testing.B)
    bench_pattern = r'^func\s+(Benchmark\w+)\s*\(\s*\w+\s+\*testing\.B\s*\)\s*\{'
    matches = re.finditer(bench_pattern, content, re.MULTILINE)
    
    for match in matches:
        func_name = match.group(1)
        line_num = content[:match.start()].count('\n') + 1
        
        func_body = _extract_function_body(content, match.start())
        
        functions.append({
            "name": func_name,
            "line": line_num,
            "file": file_path,
            "type": "benchmark",
            "has_reset_timer": 'b.ResetTimer()' in func_body,
            "has_parallel": 'b.RunParallel(' in func_body
        })
    
    return functions


def _find_example_functions(content: str, file_path: str) -> List[Dict[str, Any]]:
    """Find all example functions in the content."""
    functions = []
    
    # Pattern for example functions: func ExampleXxx()
    example_pattern = r'^func\s+(Example\w*)\s*\(\s*\)\s*\{'
    matches = re.finditer(example_pattern, content, re.MULTILINE)
    
    for match in matches:
        func_name = match.group(1)
        line_num = content[:match.start()].count('\n') + 1
        
        func_body = _extract_function_body(content, match.start())
        
        functions.append({
            "name": func_name,
            "line": line_num,
            "file": file_path,
            "type": "example",
            "has_output": '// Output:' in func_body
        })
    
    return functions


def _analyze_test_patterns(content: str, file_path: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Analyze test patterns in the content."""
    patterns = []
    
    # Check for table-driven tests
    if 'tests := []struct{' in content or 'testCases := []struct{' in content:
        patterns.append({
            "type": "table_driven",
            "file": file_path,
            "description": "Uses table-driven test pattern",
            "quality": "good"
        })
    
    # Check for setup/teardown patterns
    if 'TestMain(' in content:
        patterns.append({
            "type": "test_main",
            "file": file_path,
            "description": "Uses TestMain for setup/teardown",
            "quality": "good"
        })
    
    # Check for parallel tests
    if 't.Parallel()' in content:
        patterns.append({
            "type": "parallel",
            "file": file_path,
            "description": "Uses parallel test execution",
            "quality": "good"
        })
    
    # Check for helper functions
    if 't.Helper()' in content:
        patterns.append({
            "type": "helper",
            "file": file_path,
            "description": "Uses test helper functions",
            "quality": "good"
        })
    
    return patterns


def _check_test_issues(content: str, file_path: str, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check for common test issues."""
    issues = []
    
    # Check for missing error handling in tests
    lines = content.splitlines()
    for i, line in enumerate(lines, 1):
        if 'err :=' in line or 'err =' in line:
            # Check if error is handled
            next_lines = lines[i:i+3]  # Check next 3 lines
            if not any('if err != nil' in next_line for next_line in next_lines):
                issues.append({
                    "type": "unhandled_error",
                    "severity": "warning",
                    "line": i,
                    "file": file_path,
                    "message": "Error not handled in test",
                    "suggestion": "Add error handling: if err != nil { t.Fatal(err) }"
                })
    
    # Check for hardcoded values instead of table tests
    test_func_lines = []
    for match in re.finditer(r'^func\s+Test\w+', content, re.MULTILINE):
        test_func_lines.append(content[:match.start()].count('\n') + 1)
    
    if len(test_func_lines) > 3 and 'tests := []struct{' not in content:
        issues.append({
            "type": "missing_table_tests",
            "severity": "info",
            "file": file_path,
            "message": f"Found {len(test_func_lines)} test functions - consider using table-driven tests",
            "suggestion": "Consolidate similar tests into table-driven tests"
        })
    
    return issues


def _extract_function_body(content: str, start_pos: int) -> str:
    """Extract the body of a function from the starting position."""
    # Find the opening brace
    brace_pos = content.find('{', start_pos)
    if brace_pos == -1:
        return ""
    
    # Count braces to find the end
    brace_count = 1
    pos = brace_pos + 1
    
    while pos < len(content) and brace_count > 0:
        if content[pos] == '{':
            brace_count += 1
        elif content[pos] == '}':
            brace_count -= 1
        pos += 1
    
    return content[brace_pos:pos]


def _calculate_test_complexity(func_body: str) -> int:
    """Calculate test complexity based on control structures."""
    complexity = 1
    
    # Count control structures
    keywords = ['if', 'for', 'switch', 'select', 'case']
    for keyword in keywords:
        complexity += len(re.findall(r'\b' + keyword + r'\b', func_body))
    
    return complexity


def _find_function_definition(content: str, function_name: str) -> Optional[str]:
    """Find the function definition in the content."""
    pattern = rf'^func\s+(?:\([^)]*\)\s+)?{re.escape(function_name)}\s*\([^)]*\)(?:\s*\([^)]*\))?(?:\s+\w+)?\s*{{'
    match = re.search(pattern, content, re.MULTILINE)
    
    if match:
        return match.group(0)
    
    return None


def _parse_function_signature(func_def: str) -> Optional[Dict[str, Any]]:
    """Parse a function signature to extract parameters and return types."""
    # This is a simplified parser - in practice, you'd want a more robust one
    pattern = r'func\s+(?:\([^)]*\)\s+)?(\w+)\s*\(([^)]*)\)(?:\s*\(([^)]*)\))?(?:\s+(\w+))?'
    match = re.match(pattern, func_def)
    
    if not match:
        return None
    
    func_name = match.group(1)
    params = match.group(2) if match.group(2) else ""
    returns_paren = match.group(3) if match.group(3) else ""
    returns_single = match.group(4) if match.group(4) else ""
    
    returns = returns_paren or returns_single
    
    # Parse parameters
    param_list = []
    if params.strip():
        for param in params.split(','):
            param = param.strip()
            if param:
                parts = param.split()
                if len(parts) >= 2:
                    param_list.append({
                        "name": parts[0],
                        "type": parts[1]
                    })
    
    return {
        "name": func_name,
        "parameters": param_list,
        "returns": returns.strip() if returns else ""
    }


def _generate_table_test_code(function_name: str, signature: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Generate table-driven test code for a function."""
    test_name = f"Test{function_name}"
    
    # Build struct fields for test cases
    struct_fields = []
    call_args = []
    
    struct_fields.append("name string")
    
    for param in signature['parameters']:
        struct_fields.append(f"{param['name']} {param['type']}")
        call_args.append(f"tt.{param['name']}")
    
    # Handle return values
    if signature['returns']:
        if '(' in signature['returns']:  # Multiple returns
            return_types = signature['returns'].strip('()').split(',')
            for i, ret_type in enumerate(return_types):
                ret_type = ret_type.strip()
                if ret_type == 'error':
                    struct_fields.append("wantErr bool")
                else:
                    struct_fields.append(f"want{i+1} {ret_type}")
        else:  # Single return
            if signature['returns'] == 'error':
                struct_fields.append("wantErr bool")
            else:
                struct_fields.append(f"want {signature['returns']}")
    
    struct_def = ",\n\t\t".join(struct_fields)
    call_line = f"{function_name}({', '.join(call_args)})"
    
    # Generate the test code
    test_code = f'''func {test_name}(t *testing.T) {{
	tests := []struct {{
		{struct_def}
	}}{{
		// TODO: Add test cases.
		{{
			name: "test case 1",
			// TODO: Fill in test data
		}},
	}}
	for _, tt := range tests {{
		t.Run(tt.name, func(t *testing.T) {{'''
    
    if signature['returns']:
        if 'error' in signature['returns']:
            test_code += f'''
			got, err := {call_line}
			if (err != nil) != tt.wantErr {{
				t.Errorf("{function_name}() error = %v, wantErr %v", err, tt.wantErr)
				return
			}}
			if !tt.wantErr && !reflect.DeepEqual(got, tt.want) {{
				t.Errorf("{function_name}() = %v, want %v", got, tt.want)
			}}'''
        else:
            test_code += f'''
			if got := {call_line}; !reflect.DeepEqual(got, tt.want) {{
				t.Errorf("{function_name}() = %v, want %v", got, tt.want)
			}}'''
    else:
        test_code += f'''
			{call_line}  // TODO: Add assertions'''
    
    test_code += '''
		})
	}
}'''
    
    return test_code


def _run_coverage_analysis(path: str, config: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Run basic coverage analysis."""
    try:
        # Run go test with coverage
        result = subprocess.run(
            ['go', 'test', '-cover', './...'],
            cwd=path if os.path.isdir(path) else os.path.dirname(path),
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            output = result.stdout
            # Parse coverage percentage
            coverage_match = re.search(r'coverage: ([\d.]+)%', output)
            if coverage_match:
                return {
                    "overall_percentage": float(coverage_match.group(1)),
                    "output": output
                }
        
        return {"error": result.stderr, "output": result.stdout}
        
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return None


def _run_detailed_coverage(package_path: str, config: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Run detailed coverage analysis with per-file breakdown."""
    try:
        # Run coverage with profile output
        profile_file = "/tmp/coverage.out"
        
        # Generate coverage profile
        result1 = subprocess.run(
            ['go', 'test', f'-coverprofile={profile_file}', './...'],
            cwd=package_path,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result1.returncode != 0:
            return {"error": result1.stderr}
        
        # Get coverage by function
        result2 = subprocess.run(
            ['go', 'tool', 'cover', '-func', profile_file],
            capture_output=True,
            text=True,
            timeout=10
        )
        
        if result2.returncode == 0:
            return _parse_coverage_output(result2.stdout)
        
        return None
        
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return None


def _parse_coverage_output(output: str) -> Dict[str, Any]:
    """Parse coverage tool output."""
    lines = output.strip().split('\n')
    
    files = {}
    functions = []
    overall_coverage = 0.0
    
    for line in lines:
        if line.startswith('total:'):
            # Extract overall coverage
            match = re.search(r'([\d.]+)%', line)
            if match:
                overall_coverage = float(match.group(1))
        elif '\t' in line:
            # Function coverage line: file:line:func    coverage%
            parts = line.split('\t')
            if len(parts) >= 2:
                func_info = parts[0]
                coverage_str = parts[1]
                
                # Parse function info
                if ':' in func_info:
                    file_func = func_info.rsplit(':', 1)
                    if len(file_func) == 2:
                        file_line = file_func[0]
                        func_name = file_func[1]
                        
                        # Extract coverage percentage
                        coverage_match = re.search(r'([\d.]+)%', coverage_str)
                        if coverage_match:
                            coverage_pct = float(coverage_match.group(1))
                            
                            functions.append({
                                "file": file_line.split(':')[0] if ':' in file_line else file_line,
                                "function": func_name,
                                "coverage": coverage_pct
                            })
                            
                            # Track file coverage
                            file_name = file_line.split(':')[0] if ':' in file_line else file_line
                            if file_name not in files:
                                files[file_name] = []
                            files[file_name].append(coverage_pct)
    
    # Calculate per-file average coverage
    file_averages = {}
    for file_name, coverages in files.items():
        file_averages[file_name] = sum(coverages) / len(coverages) if coverages else 0.0
    
    return {
        "overall_coverage": overall_coverage,
        "files": file_averages,
        "functions": functions
    }


def _generate_coverage_recommendations(coverage_data: Dict[str, Any], threshold: float, config: Dict[str, Any]) -> List[str]:
    """Generate coverage improvement recommendations."""
    recommendations = []
    
    overall = coverage_data.get("overall_coverage", 0)
    
    if overall < threshold:
        recommendations.append(
            f"Overall coverage ({overall:.1f}%) is below threshold ({threshold:.1f}%). "
            "Consider adding more tests."
        )
    
    # Check file-level coverage
    files = coverage_data.get("files", {})
    low_coverage_files = [(f, c) for f, c in files.items() if c < threshold]
    
    if low_coverage_files:
        recommendations.append(
            f"Files with low coverage: {', '.join([f'{f} ({c:.1f}%)' for f, c in low_coverage_files[:3]])}"
        )
    
    # Check for untested functions
    functions = coverage_data.get("functions", [])
    untested_functions = [f for f in functions if f["coverage"] == 0]
    
    if untested_functions:
        recommendations.append(
            f"Found {len(untested_functions)} untested functions. Consider adding unit tests."
        )
    
    return recommendations


def _format_test_analysis_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the test analysis report."""
    report = "# Go Test Analysis Report\n\n"
    report += f"**Path:** `{analysis['path']}`\n\n"
    
    # Summary
    test_files = analysis['test_files']
    test_funcs = analysis['test_functions']
    bench_funcs = analysis['benchmark_functions']
    example_funcs = analysis['example_functions']
    
    report += "## Summary\n\n"
    report += f"- **Test Files:** {len(test_files)}\n"
    report += f"- **Test Functions:** {len(test_funcs)}\n"
    report += f"- **Benchmark Functions:** {len(bench_funcs)}\n"
    report += f"- **Example Functions:** {len(example_funcs)}\n\n"
    
    # Test functions details
    if test_funcs:
        report += f"## Test Functions ({len(test_funcs)})\n\n"
        for func in test_funcs:
            complexity_icon = "🔴" if func['complexity'] > 10 else "🟡" if func['complexity'] > 5 else "🟢"
            subtest_icon = "🌳" if func['has_subtests'] else ""
            report += f"- `{func['name']}` {complexity_icon} {subtest_icon}\n"
            report += f"  - File: `{func['file']}:{func['line']}`\n"
            report += f"  - Complexity: {func['complexity']}\n"
            if func['has_subtests']:
                report += f"  - Uses subtests ✅\n"
            report += "\n"
    
    # Benchmark functions
    if bench_funcs:
        report += f"## Benchmark Functions ({len(bench_funcs)})\n\n"
        for func in bench_funcs:
            report += f"- `{func['name']}`\n"
            report += f"  - File: `{func['file']}:{func['line']}`\n"
            if func['has_reset_timer']:
                report += f"  - Uses ResetTimer() ✅\n"
            if func['has_parallel']:
                report += f"  - Uses parallel benchmarking ✅\n"
            report += "\n"
    
    # Test patterns
    patterns = analysis['test_patterns']
    if patterns:
        report += f"## Test Patterns ({len(patterns)})\n\n"
        for pattern in patterns:
            quality_icon = "✅" if pattern['quality'] == 'good' else "⚠️"
            report += f"- {quality_icon} **{pattern['type']}** in `{pattern['file']}`\n"
            report += f"  {pattern['description']}\n\n"
    
    # Issues
    issues = analysis['issues']
    if issues:
        report += f"## Issues Found ({len(issues)})\n\n"
        for issue in issues:
            severity_icon = {'error': '❌', 'warning': '⚠️', 'info': '💡'}.get(issue['severity'], '💡')
            report += f"{severity_icon} **{issue['type']}**\n"
            if 'line' in issue:
                report += f"   File: `{issue['file']}:{issue['line']}`\n"
            report += f"   {issue['message']}\n"
            if 'suggestion' in issue:
                report += f"   💡 {issue['suggestion']}\n"
            report += "\n"
    
    # Coverage
    if 'coverage' in analysis:
        coverage = analysis['coverage']
        if coverage and 'overall_percentage' in coverage:
            pct = coverage['overall_percentage']
            coverage_icon = "🟢" if pct >= 80 else "🟡" if pct >= 60 else "🔴"
            report += f"## Test Coverage {coverage_icon}\n\n"
            report += f"**Overall Coverage:** {pct:.1f}%\n\n"
    
    return report


def _format_coverage_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the coverage analysis report."""
    report = "# Test Coverage Report\n\n"
    report += f"**Package:** `{analysis['package_path']}`\n"
    report += f"**Threshold:** {analysis['threshold']}%\n\n"
    
    coverage_data = analysis['coverage_data']
    if not coverage_data:
        report += "❌ No coverage data available. Ensure 'go test' works in this package.\n"
        return report
    
    if 'error' in coverage_data:
        report += f"❌ Coverage analysis failed: {coverage_data['error']}\n"
        return report
    
    # Overall coverage
    overall = coverage_data.get('overall_coverage', 0)
    threshold = analysis['threshold']
    overall_icon = "🟢" if overall >= threshold else "🟡" if overall >= threshold * 0.8 else "🔴"
    
    report += f"## Overall Coverage {overall_icon}\n\n"
    report += f"**{overall:.1f}%** (threshold: {threshold}%)\n\n"
    
    # File coverage
    files_coverage = analysis.get('files_coverage', {})
    if files_coverage:
        report += f"## File Coverage ({len(files_coverage)} files)\n\n"
        
        sorted_files = sorted(files_coverage.items(), key=lambda x: x[1])
        for file_name, coverage in sorted_files:
            file_icon = "🟢" if coverage >= threshold else "🟡" if coverage >= threshold * 0.8 else "🔴"
            report += f"- {file_icon} `{file_name}`: {coverage:.1f}%\n"
        report += "\n"
    
    # Function coverage
    functions_coverage = analysis.get('functions_coverage', [])
    if functions_coverage:
        # Show only low coverage functions
        low_coverage_funcs = [f for f in functions_coverage if f['coverage'] < threshold]
        
        if low_coverage_funcs:
            report += f"## Low Coverage Functions ({len(low_coverage_funcs)})\n\n"
            for func in sorted(low_coverage_funcs, key=lambda x: x['coverage'])[:10]:  # Top 10
                coverage_pct = func['coverage']
                func_icon = "❌" if coverage_pct == 0 else "⚠️"
                report += f"- {func_icon} `{func['function']}` in `{func['file']}`: {coverage_pct:.1f}%\n"
            
            if len(low_coverage_funcs) > 10:
                report += f"... and {len(low_coverage_funcs) - 10} more\n"
            report += "\n"
    
    # Recommendations
    recommendations = analysis['recommendations']
    if recommendations:
        report += "## Recommendations\n\n"
        for rec in recommendations:
            report += f"- 💡 {rec}\n"
    
    return report