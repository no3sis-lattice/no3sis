"""
Python Type Analysis Tools

Tools for analyzing and improving type hints in Python code.
"""

import ast
import re
import asyncio
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional, Set


async def add_type_hints(file_path: str, function_name: Optional[str] = None) -> Dict[str, Any]:
    """
    Suggest type hints for Python functions.

    Args:
        file_path: Path to Python file
        function_name: Specific function to analyze (optional)

    Returns:
        Dict with type hint suggestions
    """
    try:
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')
        tree = ast.parse(content)

        suggestions = []
        functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]

        if function_name:
            functions = [f for f in functions if f.name == function_name]

        for func in functions:
            func_suggestions = _analyze_function_for_types(func, content)
            if func_suggestions:
                suggestions.append(func_suggestions)

        return {
            "content": [{
                "type": "text",
                "text": _format_type_suggestions(suggestions)
            }],
            "success": True,
            "suggestions": suggestions
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Type hint analysis failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def check_mypy_compatibility(file_path: str) -> Dict[str, Any]:
    """
    Check Python file for mypy type checking compatibility.

    Args:
        file_path: Path to Python file

    Returns:
        Dict with mypy compatibility results
    """
    try:
        # Try to run mypy if available
        mypy_results = await _run_mypy_check(file_path)

        if mypy_results is not None:
            return {
                "content": [{
                    "type": "text",
                    "text": _format_mypy_results(mypy_results)
                }],
                "success": len(mypy_results.get("errors", [])) == 0,
                "mypy_results": mypy_results
            }

        # Fallback to manual analysis
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')
        tree = ast.parse(content)

        compatibility = _analyze_mypy_compatibility(tree, content)

        return {
            "content": [{
                "type": "text",
                "text": _format_compatibility_analysis(compatibility)
            }],
            "success": compatibility["score"] > 0.7,
            "compatibility": compatibility
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ MyPy compatibility check failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_types(code_snippet: str, context: str = "function") -> Dict[str, Any]:
    """
    Suggest appropriate types for a code snippet.

    Args:
        code_snippet: Python code to analyze
        context: Context of the code (function, class, module)

    Returns:
        Dict with type suggestions
    """
    try:
        tree = ast.parse(code_snippet)
        type_suggestions = []

        if context == "function":
            functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
            for func in functions:
                suggestions = _suggest_function_types(func, code_snippet)
                type_suggestions.extend(suggestions)

        elif context == "class":
            classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]
            for cls in classes:
                suggestions = _suggest_class_types(cls, code_snippet)
                type_suggestions.extend(suggestions)

        else:  # module or general
            suggestions = _suggest_general_types(tree, code_snippet)
            type_suggestions.extend(suggestions)

        return {
            "content": [{
                "type": "text",
                "text": _format_type_suggestions_inline(type_suggestions)
            }],
            "success": True,
            "type_suggestions": type_suggestions
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Type suggestion failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def _run_mypy_check(file_path: str) -> Optional[Dict[str, Any]]:
    """Run mypy type checker if available."""
    try:
        process = await asyncio.create_subprocess_exec(
            "mypy", "--show-error-codes", "--no-error-summary", file_path,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )

        stdout, stderr = await process.communicate()

        output = stdout.decode() + stderr.decode()
        errors = []

        for line in output.split('\n'):
            if line.strip() and ':' in line:
                parts = line.split(':', 3)
                if len(parts) >= 4:
                    errors.append({
                        "line": parts[1],
                        "column": parts[2],
                        "message": parts[3].strip(),
                        "severity": "error" if "error:" in line else "warning"
                    })

        return {
            "errors": errors,
            "success": process.returncode == 0
        }

    except FileNotFoundError:
        return None


def _analyze_function_for_types(func: ast.FunctionDef, content: str) -> Optional[Dict[str, Any]]:
    """Analyze a function for type hint opportunities."""
    suggestions = []

    # Check parameters
    for arg in func.args.args:
        if arg.annotation is None:
            param_type = _infer_parameter_type(arg.arg, func, content)
            if param_type:
                suggestions.append({
                    "element": "parameter",
                    "name": arg.arg,
                    "suggested_type": param_type,
                    "reason": "Inferred from usage"
                })

    # Check return type
    if func.returns is None:
        return_type = _infer_return_type(func, content)
        if return_type:
            suggestions.append({
                "element": "return",
                "suggested_type": return_type,
                "reason": "Inferred from return statements"
            })

    return {
        "function": func.name,
        "line": func.lineno,
        "suggestions": suggestions
    } if suggestions else None


def _infer_parameter_type(param_name: str, func: ast.FunctionDef, content: str) -> Optional[str]:
    """Infer parameter type from usage within function."""
    # Look for common patterns
    for node in ast.walk(func):
        if isinstance(node, ast.Compare):
            if (isinstance(node.left, ast.Name) and
                node.left.id == param_name):

                # Check for None comparison
                if any(isinstance(comp, ast.Constant) and comp.value is None
                       for comp in node.comparators):
                    return "Optional[Any]"

        # Check for method calls that indicate type
        elif isinstance(node, ast.Call):
            if (isinstance(node.func, ast.Attribute) and
                isinstance(node.func.value, ast.Name) and
                node.func.value.id == param_name):

                method = node.func.attr
                if method in ["append", "extend", "pop"]:
                    return "List[Any]"
                elif method in ["add", "remove", "discard"]:
                    return "Set[Any]"
                elif method in ["keys", "values", "items", "get"]:
                    return "Dict[Any, Any]"
                elif method in ["decode", "encode", "split", "join"]:
                    return "str"

    return None


def _infer_return_type(func: ast.FunctionDef, content: str) -> Optional[str]:
    """Infer return type from return statements."""
    return_types = set()

    for node in ast.walk(func):
        if isinstance(node, ast.Return):
            if node.value is None:
                return_types.add("None")
            elif isinstance(node.value, ast.Constant):
                if isinstance(node.value.value, str):
                    return_types.add("str")
                elif isinstance(node.value.value, int):
                    return_types.add("int")
                elif isinstance(node.value.value, float):
                    return_types.add("float")
                elif isinstance(node.value.value, bool):
                    return_types.add("bool")
            elif isinstance(node.value, ast.List):
                return_types.add("List[Any]")
            elif isinstance(node.value, ast.Dict):
                return_types.add("Dict[Any, Any]")

    if len(return_types) == 1:
        return list(return_types)[0]
    elif len(return_types) > 1:
        if "None" in return_types:
            other_types = return_types - {"None"}
            if len(other_types) == 1:
                return f"Optional[{list(other_types)[0]}]"
        return "Union[" + ", ".join(sorted(return_types)) + "]"

    return None


def _analyze_mypy_compatibility(tree: ast.AST, content: str) -> Dict[str, Any]:
    """Analyze code for mypy compatibility."""
    issues = []
    score = 1.0

    # Check for Any usage
    any_usage = _count_any_usage(tree)
    if any_usage > 0:
        issues.append(f"Using 'Any' {any_usage} times - reduces type safety")
        score -= 0.1 * any_usage

    # Check for missing type hints
    functions = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    untyped_functions = [f for f in functions if not _has_type_hints(f)]

    if untyped_functions:
        issues.append(f"{len(untyped_functions)} functions missing type hints")
        score -= 0.2 * len(untyped_functions) / len(functions) if functions else 0

    # Check for dynamic attribute access
    dynamic_attrs = _count_dynamic_attributes(tree)
    if dynamic_attrs > 0:
        issues.append(f"{dynamic_attrs} dynamic attribute accesses found")
        score -= 0.05 * dynamic_attrs

    return {
        "score": max(0.0, score),
        "issues": issues,
        "total_functions": len(functions),
        "typed_functions": len(functions) - len(untyped_functions)
    }


def _suggest_function_types(func: ast.FunctionDef, code: str) -> List[Dict[str, Any]]:
    """Suggest types for a specific function."""
    suggestions = []

    for arg in func.args.args:
        if arg.annotation is None:
            suggestions.append({
                "type": "parameter",
                "name": arg.arg,
                "line": func.lineno,
                "suggestion": "Add type annotation",
                "example": f"{arg.arg}: Any"
            })

    if func.returns is None:
        suggestions.append({
            "type": "return",
            "name": func.name,
            "line": func.lineno,
            "suggestion": "Add return type annotation",
            "example": f"-> Any"
        })

    return suggestions


def _suggest_class_types(cls: ast.ClassDef, code: str) -> List[Dict[str, Any]]:
    """Suggest types for class attributes and methods."""
    suggestions = []

    # Check methods
    for node in cls.body:
        if isinstance(node, ast.FunctionDef):
            method_suggestions = _suggest_function_types(node, code)
            suggestions.extend(method_suggestions)

    # Check for class variables that could be typed
    for node in cls.body:
        if isinstance(node, ast.AnnAssign) and node.annotation is None:
            if isinstance(node.target, ast.Name):
                suggestions.append({
                    "type": "class_variable",
                    "name": node.target.id,
                    "line": node.lineno,
                    "suggestion": "Add type annotation",
                    "example": f"{node.target.id}: Any"
                })

    return suggestions


def _suggest_general_types(tree: ast.AST, code: str) -> List[Dict[str, Any]]:
    """Suggest types for module-level code."""
    suggestions = []

    # Check module-level variables
    for node in ast.walk(tree):
        if isinstance(node, ast.AnnAssign) and node.annotation is None:
            if isinstance(node.target, ast.Name):
                suggestions.append({
                    "type": "variable",
                    "name": node.target.id,
                    "line": node.lineno,
                    "suggestion": "Add type annotation",
                    "example": f"{node.target.id}: Any"
                })

    return suggestions


def _count_any_usage(tree: ast.AST) -> int:
    """Count usage of 'Any' type."""
    count = 0
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id == "Any":
            count += 1
    return count


def _has_type_hints(func: ast.FunctionDef) -> bool:
    """Check if function has type hints."""
    has_param_hints = any(arg.annotation is not None for arg in func.args.args)
    has_return_hint = func.returns is not None
    return has_param_hints or has_return_hint


def _count_dynamic_attributes(tree: ast.AST) -> int:
    """Count dynamic attribute accesses (getattr, setattr, etc.)."""
    count = 0
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                if node.func.id in ["getattr", "setattr", "hasattr", "delattr"]:
                    count += 1
    return count


def _format_type_suggestions(suggestions: List[Dict[str, Any]]) -> str:
    """Format type hint suggestions."""
    if not suggestions:
        return "✅ All functions appear to have appropriate type hints"

    result = [f"🔧 Found type hint opportunities in {len(suggestions)} functions:"]

    for func_suggestion in suggestions:
        result.append(f"\n📍 {func_suggestion['function']} (line {func_suggestion['line']}):")

        for suggestion in func_suggestion['suggestions']:
            if suggestion['element'] == 'parameter':
                result.append(f"  Parameter '{suggestion['name']}': {suggestion['suggested_type']}")
            elif suggestion['element'] == 'return':
                result.append(f"  Return type: {suggestion['suggested_type']}")

    return "\n".join(result)


def _format_mypy_results(results: Dict[str, Any]) -> str:
    """Format mypy check results."""
    errors = results.get("errors", [])

    if not errors:
        return "✅ MyPy type checking passed - no issues found"

    result = [f"⚠️ MyPy found {len(errors)} type issues:"]

    for error in errors[:10]:  # Show first 10 errors
        result.append(f"  Line {error['line']}: {error['message']}")

    if len(errors) > 10:
        result.append(f"  ... and {len(errors) - 10} more issues")

    return "\n".join(result)


def _format_compatibility_analysis(compatibility: Dict[str, Any]) -> str:
    """Format compatibility analysis results."""
    score = compatibility["score"]
    issues = compatibility["issues"]

    result = [f"📊 MyPy Compatibility Score: {score:.1%}"]

    if score > 0.8:
        result.append("✅ Good type safety")
    elif score > 0.6:
        result.append("⚠️ Moderate type safety")
    else:
        result.append("❌ Poor type safety")

    if issues:
        result.append("\n🔍 Issues found:")
        for issue in issues:
            result.append(f"  - {issue}")

    result.append(f"\n📈 Progress: {compatibility['typed_functions']}/{compatibility['total_functions']} functions typed")

    return "\n".join(result)


def _format_type_suggestions_inline(suggestions: List[Dict[str, Any]]) -> str:
    """Format type suggestions for inline code."""
    if not suggestions:
        return "✅ No additional type hints suggested"

    result = [f"🔧 Type hint suggestions ({len(suggestions)}):"]

    for suggestion in suggestions:
        result.append(f"  {suggestion['type'].title()} '{suggestion['name']}': {suggestion['suggestion']}")
        if 'example' in suggestion:
            result.append(f"    Example: {suggestion['example']}")

    return "\n".join(result)