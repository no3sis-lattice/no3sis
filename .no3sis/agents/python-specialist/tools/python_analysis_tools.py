"""
Python Code Analysis Tools

Core functionality for analyzing Python code quality, patterns, and performance.
"""

import ast
import re
import sys
import asyncio
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple
import tempfile


async def analyze_code(file_path: str, analysis_type: str = "full") -> Dict[str, Any]:
    """
    Analyze Python code for various quality metrics.

    Args:
        file_path: Path to Python file to analyze
        analysis_type: Type of analysis (full, syntax, complexity, imports)

    Returns:
        Dict with analysis results
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

        if not path.suffix == '.py':
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ Not a Python file: {file_path}"
                }],
                "success": False,
                "error": "not_python_file"
            }

        content = path.read_text(encoding='utf-8')

        if analysis_type == "syntax":
            analysis = _analyze_syntax(content, str(path))
        elif analysis_type == "complexity":
            analysis = _analyze_complexity(content)
        elif analysis_type == "imports":
            analysis = _analyze_imports(content)
        else:  # full
            analysis = await _analyze_full(content, str(path))

        return {
            "content": [{
                "type": "text",
                "text": _format_analysis_results(analysis, analysis_type)
            }],
            "success": True,
            "analysis": analysis,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def check_pep8(file_path: str, fix_suggestions: bool = True) -> Dict[str, Any]:
    """
    Check Python code against PEP 8 standards.

    Args:
        file_path: Path to Python file
        fix_suggestions: Whether to include fix suggestions

    Returns:
        Dict with PEP 8 compliance results
    """
    try:
        path = Path(file_path)

        if not path.exists() or not path.suffix == '.py':
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Invalid Python file: {file_path}"
                }],
                "success": False
            }

        # Use ruff for modern Python linting (fallback to basic checks if not available)
        pep8_issues = await _check_with_ruff(str(path))

        if not pep8_issues:
            # Fallback to basic AST-based checks
            content = path.read_text(encoding='utf-8')
            pep8_issues = _basic_pep8_checks(content)

        suggestions = []
        if fix_suggestions and pep8_issues:
            suggestions = _generate_pep8_fixes(pep8_issues)

        return {
            "content": [{
                "type": "text",
                "text": _format_pep8_results(pep8_issues, suggestions)
            }],
            "success": len(pep8_issues) == 0,
            "issues": pep8_issues,
            "suggestions": suggestions
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ PEP 8 check failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_refactors(file_path: str, focus: str = "all") -> Dict[str, Any]:
    """
    Suggest refactoring opportunities for Python code.

    Args:
        file_path: Path to Python file
        focus: Focus area (all, performance, readability, structure)

    Returns:
        Dict with refactoring suggestions
    """
    try:
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')

        tree = ast.parse(content)
        refactors = []

        if focus in ["all", "structure"]:
            refactors.extend(_suggest_structural_refactors(tree, content))

        if focus in ["all", "performance"]:
            refactors.extend(_suggest_performance_refactors(tree, content))

        if focus in ["all", "readability"]:
            refactors.extend(_suggest_readability_refactors(tree, content))

        return {
            "content": [{
                "type": "text",
                "text": _format_refactor_suggestions(refactors, focus)
            }],
            "success": True,
            "refactors": refactors,
            "focus": focus
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Refactor analysis failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def profile_performance(file_path: str, function_name: Optional[str] = None) -> Dict[str, Any]:
    """
    Analyze Python code for performance bottlenecks.

    Args:
        file_path: Path to Python file
        function_name: Specific function to profile (optional)

    Returns:
        Dict with performance analysis
    """
    try:
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')

        tree = ast.parse(content)
        performance_issues = []

        # Static analysis for common performance issues
        performance_issues.extend(_detect_performance_antipatterns(tree, content))
        performance_issues.extend(_detect_inefficient_loops(tree))
        performance_issues.extend(_detect_memory_issues(tree))

        # Calculate complexity metrics
        complexity = _calculate_complexity_metrics(tree)

        return {
            "content": [{
                "type": "text",
                "text": _format_performance_analysis(performance_issues, complexity)
            }],
            "success": True,
            "performance_issues": performance_issues,
            "complexity_metrics": complexity
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Performance analysis failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


def _analyze_syntax(content: str, file_path: str) -> Dict[str, Any]:
    """Analyze Python syntax and basic structure."""
    try:
        tree = ast.parse(content)

        return {
            "valid_syntax": True,
            "ast_nodes": len(list(ast.walk(tree))),
            "functions": len([n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]),
            "classes": len([n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]),
            "imports": len([n for n in ast.walk(tree) if isinstance(n, (ast.Import, ast.ImportFrom))])
        }
    except SyntaxError as e:
        return {
            "valid_syntax": False,
            "error": str(e),
            "line": e.lineno,
            "column": e.offset
        }


def _analyze_complexity(content: str) -> Dict[str, Any]:
    """Analyze code complexity metrics."""
    tree = ast.parse(content)

    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]

    complexity_metrics = {
        "cyclomatic_complexity": _calculate_cyclomatic_complexity(tree),
        "function_count": len(functions),
        "class_count": len(classes),
        "max_function_length": max([_count_lines(f) for f in functions], default=0),
        "avg_function_length": sum([_count_lines(f) for f in functions]) / len(functions) if functions else 0
    }

    return complexity_metrics


def _analyze_imports(content: str) -> Dict[str, Any]:
    """Analyze import patterns and dependencies."""
    tree = ast.parse(content)

    imports = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                imports.append({"type": "import", "module": alias.name, "alias": alias.asname})
        elif isinstance(node, ast.ImportFrom):
            module = node.module or ""
            for alias in node.names:
                imports.append({"type": "from_import", "module": module, "name": alias.name, "alias": alias.asname})

    return {
        "total_imports": len(imports),
        "import_types": {
            "standard": [imp for imp in imports if _is_standard_library(imp["module"])],
            "third_party": [imp for imp in imports if not _is_standard_library(imp["module"])],
        },
        "unused_imports": [],  # Would need more sophisticated analysis
        "imports": imports
    }


async def _analyze_full(content: str, file_path: str) -> Dict[str, Any]:
    """Perform comprehensive code analysis."""
    syntax_analysis = _analyze_syntax(content, file_path)
    complexity_analysis = _analyze_complexity(content)
    import_analysis = _analyze_imports(content)

    # Additional checks
    tree = ast.parse(content)
    type_hints = _check_type_annotations(tree)
    docstrings = _check_docstrings(tree)

    return {
        "syntax": syntax_analysis,
        "complexity": complexity_analysis,
        "imports": import_analysis,
        "type_hints": type_hints,
        "docstrings": docstrings,
        "lines_of_code": len(content.splitlines()),
        "file_size": len(content)
    }


async def _check_with_ruff(file_path: str) -> List[Dict[str, Any]]:
    """Check file with ruff linter if available."""
    try:
        result = await asyncio.create_subprocess_exec(
            "ruff", "check", "--output-format", "json", file_path,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )

        stdout, stderr = await result.communicate()

        if result.returncode == 0:
            return []  # No issues

        # Parse ruff JSON output
        try:
            import json
            issues = json.loads(stdout.decode())
            return issues
        except:
            return []

    except FileNotFoundError:
        return []  # Ruff not available


def _basic_pep8_checks(content: str) -> List[Dict[str, Any]]:
    """Basic PEP 8 checks using regex patterns."""
    issues = []
    lines = content.splitlines()

    for i, line in enumerate(lines, 1):
        # Long lines
        if len(line) > 88:  # Using 88 as black's default
            issues.append({
                "line": i,
                "code": "E501",
                "message": f"Line too long ({len(line)} > 88 characters)"
            })

        # Trailing whitespace
        if line.rstrip() != line:
            issues.append({
                "line": i,
                "code": "W291",
                "message": "Trailing whitespace"
            })

        # Multiple spaces after operator
        if re.search(r'[=+\-*/]  +', line):
            issues.append({
                "line": i,
                "code": "E221",
                "message": "Multiple spaces after operator"
            })

    return issues


def _generate_pep8_fixes(issues: List[Dict[str, Any]]) -> List[str]:
    """Generate fix suggestions for PEP 8 issues."""
    suggestions = []

    for issue in issues:
        code = issue.get("code", "")
        if code == "E501":
            suggestions.append("Break long lines using parentheses or line continuation")
        elif code == "W291":
            suggestions.append("Remove trailing whitespace")
        elif code == "E221":
            suggestions.append("Use single space around operators")

    return list(set(suggestions))  # Remove duplicates


def _suggest_structural_refactors(tree: ast.AST, content: str) -> List[Dict[str, Any]]:
    """Suggest structural improvements."""
    refactors = []

    # Large functions
    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    for func in functions:
        lines = _count_lines(func)
        if lines > 50:
            refactors.append({
                "type": "structure",
                "target": func.name,
                "issue": f"Function '{func.name}' is too long ({lines} lines)",
                "suggestion": "Consider breaking into smaller functions"
            })

    # Classes with too many methods
    classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]
    for cls in classes:
        methods = [n for n in cls.body if isinstance(n, ast.FunctionDef)]
        if len(methods) > 20:
            refactors.append({
                "type": "structure",
                "target": cls.name,
                "issue": f"Class '{cls.name}' has {len(methods)} methods",
                "suggestion": "Consider splitting into smaller classes"
            })

    return refactors


def _suggest_performance_refactors(tree: ast.AST, content: str) -> List[Dict[str, Any]]:
    """Suggest performance improvements."""
    refactors = []

    # Check for list comprehensions that could be generator expressions
    for node in ast.walk(tree):
        if isinstance(node, ast.ListComp):
            refactors.append({
                "type": "performance",
                "target": f"Line {node.lineno}",
                "issue": "List comprehension could be generator expression",
                "suggestion": "Use () instead of [] for memory efficiency if iterating once"
            })

    return refactors


def _suggest_readability_refactors(tree: ast.AST, content: str) -> List[Dict[str, Any]]:
    """Suggest readability improvements."""
    refactors = []

    # Check for missing docstrings
    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    for func in functions:
        if not ast.get_docstring(func):
            refactors.append({
                "type": "readability",
                "target": func.name,
                "issue": f"Function '{func.name}' missing docstring",
                "suggestion": "Add descriptive docstring with parameters and return value"
            })

    return refactors


def _detect_performance_antipatterns(tree: ast.AST, content: str) -> List[Dict[str, Any]]:
    """Detect common performance anti-patterns."""
    issues = []

    for node in ast.walk(tree):
        # String concatenation in loops
        if isinstance(node, ast.For):
            for child in ast.walk(node):
                if isinstance(child, ast.AugAssign) and isinstance(child.op, ast.Add):
                    if isinstance(child.target, ast.Name) and isinstance(child.value, ast.Constant):
                        issues.append({
                            "type": "performance",
                            "line": node.lineno,
                            "issue": "String concatenation in loop",
                            "suggestion": "Use join() or list accumulation instead"
                        })

    return issues


def _detect_inefficient_loops(tree: ast.AST) -> List[Dict[str, Any]]:
    """Detect inefficient loop patterns."""
    issues = []

    for node in ast.walk(tree):
        if isinstance(node, ast.For):
            # Check for range(len(seq)) pattern
            if (isinstance(node.iter, ast.Call) and
                isinstance(node.iter.func, ast.Name) and
                node.iter.func.id == 'range' and
                len(node.iter.args) == 1 and
                isinstance(node.iter.args[0], ast.Call) and
                isinstance(node.iter.args[0].func, ast.Name) and
                node.iter.args[0].func.id == 'len'):

                issues.append({
                    "type": "loop_efficiency",
                    "line": node.lineno,
                    "issue": "Using range(len(seq)) pattern",
                    "suggestion": "Use enumerate() for index and value, or iterate directly"
                })

    return issues


def _detect_memory_issues(tree: ast.AST) -> List[Dict[str, Any]]:
    """Detect potential memory issues."""
    issues = []

    for node in ast.walk(tree):
        # Large list/dict comprehensions
        if isinstance(node, (ast.ListComp, ast.DictComp)):
            # This is a simplified check - would need more context for real analysis
            issues.append({
                "type": "memory",
                "line": node.lineno,
                "issue": "Large comprehension detected",
                "suggestion": "Consider using generator expressions for large datasets"
            })

    return issues


def _calculate_complexity_metrics(tree: ast.AST) -> Dict[str, Any]:
    """Calculate various complexity metrics."""
    return {
        "cyclomatic_complexity": _calculate_cyclomatic_complexity(tree),
        "depth": _calculate_max_depth(tree),
        "nodes": len(list(ast.walk(tree)))
    }


def _calculate_cyclomatic_complexity(tree: ast.AST) -> int:
    """Calculate cyclomatic complexity."""
    complexity = 1  # Base complexity

    for node in ast.walk(tree):
        if isinstance(node, (ast.If, ast.While, ast.For, ast.ExceptHandler)):
            complexity += 1
        elif isinstance(node, ast.BoolOp):
            complexity += len(node.values) - 1

    return complexity


def _calculate_max_depth(tree: ast.AST, depth: int = 0) -> int:
    """Calculate maximum nesting depth."""
    max_depth = depth

    for child in ast.iter_child_nodes(tree):
        if isinstance(child, (ast.If, ast.While, ast.For, ast.With, ast.Try)):
            child_depth = _calculate_max_depth(child, depth + 1)
            max_depth = max(max_depth, child_depth)

    return max_depth


def _count_lines(node: ast.AST) -> int:
    """Count lines in AST node."""
    if hasattr(node, 'end_lineno') and hasattr(node, 'lineno'):
        return node.end_lineno - node.lineno + 1
    return 1


def _check_type_annotations(tree: ast.AST) -> Dict[str, Any]:
    """Check for type annotations."""
    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]

    annotated_functions = 0
    total_parameters = 0
    annotated_parameters = 0

    for func in functions:
        has_return_annotation = func.returns is not None

        param_count = len(func.args.args)
        total_parameters += param_count

        annotated_params = sum(1 for arg in func.args.args if arg.annotation is not None)
        annotated_parameters += annotated_params

        if has_return_annotation and annotated_params == param_count:
            annotated_functions += 1

    return {
        "total_functions": len(functions),
        "annotated_functions": annotated_functions,
        "annotation_coverage": annotated_functions / len(functions) if functions else 0,
        "parameter_annotation_coverage": annotated_parameters / total_parameters if total_parameters else 0
    }


def _check_docstrings(tree: ast.AST) -> Dict[str, Any]:
    """Check for docstrings."""
    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]

    functions_with_docstrings = sum(1 for func in functions if ast.get_docstring(func))
    classes_with_docstrings = sum(1 for cls in classes if ast.get_docstring(cls))

    return {
        "function_docstring_coverage": functions_with_docstrings / len(functions) if functions else 0,
        "class_docstring_coverage": classes_with_docstrings / len(classes) if classes else 0,
        "functions_with_docstrings": functions_with_docstrings,
        "classes_with_docstrings": classes_with_docstrings
    }


def _is_standard_library(module_name: str) -> bool:
    """Check if module is part of Python standard library."""
    stdlib_modules = {
        'os', 'sys', 'json', 'urllib', 'http', 'datetime', 'collections',
        'itertools', 'functools', 'operator', 'pathlib', 'tempfile',
        'subprocess', 'threading', 'asyncio', 're', 'math', 'random'
    }

    # Get the root module name
    root_module = module_name.split('.')[0]
    return root_module in stdlib_modules


def _format_analysis_results(analysis: Dict[str, Any], analysis_type: str) -> str:
    """Format analysis results for display."""
    if analysis_type == "syntax":
        if analysis.get("valid_syntax"):
            return f"✅ Valid Python syntax\n" \
                   f"Functions: {analysis.get('functions', 0)}\n" \
                   f"Classes: {analysis.get('classes', 0)}\n" \
                   f"Imports: {analysis.get('imports', 0)}"
        else:
            return f"❌ Syntax Error: {analysis.get('error')}\n" \
                   f"Line {analysis.get('line')}, Column {analysis.get('column')}"

    elif analysis_type == "complexity":
        return f"📊 Complexity Analysis:\n" \
               f"Cyclomatic Complexity: {analysis.get('cyclomatic_complexity', 0)}\n" \
               f"Functions: {analysis.get('function_count', 0)}\n" \
               f"Classes: {analysis.get('class_count', 0)}\n" \
               f"Max Function Length: {analysis.get('max_function_length', 0)} lines"

    elif analysis_type == "imports":
        return f"📦 Import Analysis:\n" \
               f"Total Imports: {analysis.get('total_imports', 0)}\n" \
               f"Standard Library: {len(analysis.get('import_types', {}).get('standard', []))}\n" \
               f"Third Party: {len(analysis.get('import_types', {}).get('third_party', []))}"

    else:  # full
        return f"🔍 Full Analysis Complete:\n" \
               f"Lines of Code: {analysis.get('lines_of_code', 0)}\n" \
               f"Functions: {analysis.get('syntax', {}).get('functions', 0)}\n" \
               f"Classes: {analysis.get('syntax', {}).get('classes', 0)}\n" \
               f"Type Annotation Coverage: {analysis.get('type_hints', {}).get('annotation_coverage', 0):.1%}\n" \
               f"Docstring Coverage: {analysis.get('docstrings', {}).get('function_docstring_coverage', 0):.1%}"


def _format_pep8_results(issues: List[Dict[str, Any]], suggestions: List[str]) -> str:
    """Format PEP 8 check results."""
    if not issues:
        return "✅ PEP 8 compliant - no issues found"

    result = [f"⚠️ Found {len(issues)} PEP 8 issues:"]

    for issue in issues[:10]:  # Show first 10 issues
        result.append(f"  Line {issue.get('line')}: {issue.get('message')} [{issue.get('code')}]")

    if len(issues) > 10:
        result.append(f"  ... and {len(issues) - 10} more issues")

    if suggestions:
        result.append("\n💡 Fix suggestions:")
        for suggestion in suggestions:
            result.append(f"  - {suggestion}")

    return "\n".join(result)


def _format_refactor_suggestions(refactors: List[Dict[str, Any]], focus: str) -> str:
    """Format refactoring suggestions."""
    if not refactors:
        return f"✅ No {focus} refactoring suggestions found"

    result = [f"🔧 Found {len(refactors)} refactoring opportunities ({focus}):"]

    for refactor in refactors:
        result.append(f"  {refactor['target']}: {refactor['issue']}")
        result.append(f"    💡 {refactor['suggestion']}")

    return "\n".join(result)


def _format_performance_analysis(issues: List[Dict[str, Any]], complexity: Dict[str, Any]) -> str:
    """Format performance analysis results."""
    result = [f"⚡ Performance Analysis:"]

    result.append(f"Complexity: {complexity.get('cyclomatic_complexity', 0)}")
    result.append(f"Max Depth: {complexity.get('depth', 0)}")
    result.append(f"Total Nodes: {complexity.get('nodes', 0)}")

    if issues:
        result.append(f"\n⚠️ Found {len(issues)} performance issues:")
        for issue in issues:
            result.append(f"  Line {issue.get('line')}: {issue['issue']}")
            result.append(f"    💡 {issue['suggestion']}")
    else:
        result.append("\n✅ No obvious performance issues detected")

    return "\n".join(result)