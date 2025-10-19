"""
TypeScript Code Analysis Tools

Core functionality for analyzing TypeScript/JavaScript code quality, patterns, and structure.
"""

import json
import re
import sys
import asyncio
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple
import tempfile


async def analyze_typescript_code(file_path: str, analysis_type: str = "full") -> Dict[str, Any]:
    """
    Analyze TypeScript/JavaScript code for various quality metrics.

    Args:
        file_path: Path to TypeScript/JavaScript file to analyze
        analysis_type: Type of analysis (full, syntax, complexity, imports, types)

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

        if analysis_type == "syntax":
            analysis = await _analyze_syntax(content, str(path))
        elif analysis_type == "complexity":
            analysis = await _analyze_complexity(content)
        elif analysis_type == "imports":
            analysis = await _analyze_imports(content)
        elif analysis_type == "types":
            analysis = await _analyze_types(content, str(path))
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


async def check_eslint_compliance(file_path: str, fix_suggestions: bool = True) -> Dict[str, Any]:
    """
    Check TypeScript/JavaScript code against ESLint rules.

    Args:
        file_path: Path to TypeScript/JavaScript file
        fix_suggestions: Whether to include fix suggestions

    Returns:
        Dict with ESLint compliance results
    """
    try:
        path = Path(file_path)

        if not path.exists() or path.suffix not in ['.ts', '.tsx', '.js', '.jsx']:
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Invalid TypeScript/JavaScript file: {file_path}"
                }],
                "success": False,
                "error": "invalid_file"
            }

        # Try to run ESLint if available
        eslint_result = await _run_eslint(str(path))

        if eslint_result is None:
            # Fallback to manual analysis
            content = path.read_text(encoding='utf-8')
            eslint_result = await _analyze_eslint_patterns(content, str(path))

        suggestions = []
        if fix_suggestions and eslint_result.get("issues"):
            suggestions = await _generate_eslint_fixes(eslint_result["issues"], str(path))

        formatted_output = _format_eslint_results(eslint_result, suggestions, fix_suggestions)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "eslint_result": eslint_result,
            "suggestions": suggestions,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ ESLint check failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_refactors(file_path: str, focus: str = "all") -> Dict[str, Any]:
    """
    Suggest refactoring opportunities for TypeScript/JavaScript code.

    Args:
        file_path: Path to TypeScript/JavaScript file
        focus: Focus area (all, performance, readability, types, patterns)

    Returns:
        Dict with refactoring suggestions
    """
    try:
        path = Path(file_path)

        if not path.exists() or path.suffix not in ['.ts', '.tsx', '.js', '.jsx']:
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Invalid TypeScript/JavaScript file: {file_path}"
                }],
                "success": False,
                "error": "invalid_file"
            }

        content = path.read_text(encoding='utf-8')

        refactor_suggestions = await _analyze_refactoring_opportunities(content, str(path), focus)

        formatted_output = _format_refactor_suggestions(refactor_suggestions, focus)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "suggestions": refactor_suggestions,
            "focus": focus,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Refactor analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

async def _analyze_syntax(content: str, file_path: str) -> Dict[str, Any]:
    """Analyze basic syntax and structure."""
    lines = content.split('\n')

    # Try TypeScript compiler if available
    ts_check = await _run_typescript_check(content, file_path)

    return {
        "line_count": len(lines),
        "character_count": len(content),
        "is_typescript": file_path.endswith(('.ts', '.tsx')),
        "syntax_errors": ts_check.get("errors", []) if ts_check else [],
        "imports": _extract_imports(content),
        "exports": _extract_exports(content),
        "functions": _extract_functions(content),
        "classes": _extract_classes(content)
    }


async def _analyze_complexity(content: str) -> Dict[str, Any]:
    """Analyze code complexity metrics."""
    lines = content.split('\n')
    non_empty_lines = [line.strip() for line in lines if line.strip()]

    # Cyclomatic complexity estimation
    complexity_keywords = ['if', 'else', 'for', 'while', 'switch', 'case', 'catch', '&&', '||', '?']
    complexity_score = 1  # Base complexity

    for line in non_empty_lines:
        for keyword in complexity_keywords:
            complexity_score += line.count(keyword)

    # Function complexity
    functions = _extract_functions(content)
    function_complexities = []

    for func in functions:
        func_complexity = 1
        func_content = func.get("body", "")
        for keyword in complexity_keywords:
            func_complexity += func_content.count(keyword)
        function_complexities.append({
            "name": func.get("name", "anonymous"),
            "complexity": func_complexity,
            "line": func.get("line", 0)
        })

    return {
        "total_lines": len(lines),
        "code_lines": len(non_empty_lines),
        "cyclomatic_complexity": complexity_score,
        "function_count": len(functions),
        "function_complexities": function_complexities,
        "max_function_complexity": max([f["complexity"] for f in function_complexities]) if function_complexities else 0
    }


async def _analyze_imports(content: str) -> Dict[str, Any]:
    """Analyze import patterns and dependencies."""
    imports = _extract_imports(content)

    # Categorize imports
    relative_imports = [imp for imp in imports if imp.get("source", "").startswith("./") or imp.get("source", "").startswith("../")]
    external_imports = [imp for imp in imports if not imp.get("source", "").startswith(".")]

    # Detect common patterns
    react_imports = [imp for imp in external_imports if "react" in imp.get("source", "").lower()]
    node_imports = [imp for imp in external_imports if imp.get("source", "") in ["fs", "path", "os", "crypto", "http", "https"]]

    return {
        "total_imports": len(imports),
        "relative_imports": len(relative_imports),
        "external_imports": len(external_imports),
        "react_detected": len(react_imports) > 0,
        "node_detected": len(node_imports) > 0,
        "import_details": imports,
        "unused_imports": []  # Would require more complex analysis
    }


async def _analyze_types(content: str, file_path: str) -> Dict[str, Any]:
    """Analyze TypeScript type usage and safety."""
    if not file_path.endswith(('.ts', '.tsx')):
        return {"message": "Type analysis only available for TypeScript files"}

    # Count type annotations
    type_annotations = len(re.findall(r':\s*\w+', content))
    any_usage = len(re.findall(r':\s*any\b', content))
    unknown_usage = len(re.findall(r':\s*unknown\b', content))

    # Interface and type definitions
    interfaces = len(re.findall(r'interface\s+\w+', content))
    type_aliases = len(re.findall(r'type\s+\w+\s*=', content))

    # Generic usage
    generics = len(re.findall(r'<\w+(?:\s*extends\s*\w+)?>', content))

    return {
        "type_annotations": type_annotations,
        "any_usage": any_usage,
        "unknown_usage": unknown_usage,
        "interfaces": interfaces,
        "type_aliases": type_aliases,
        "generics": generics,
        "type_safety_score": max(0, 100 - (any_usage * 10))  # Rough score
    }


async def _analyze_full(content: str, file_path: str) -> Dict[str, Any]:
    """Perform comprehensive analysis."""
    syntax = await _analyze_syntax(content, file_path)
    complexity = await _analyze_complexity(content)
    imports = await _analyze_imports(content)
    types = await _analyze_types(content, file_path)

    return {
        "syntax": syntax,
        "complexity": complexity,
        "imports": imports,
        "types": types,
        "overall_score": _calculate_overall_score(complexity, types, imports)
    }


def _extract_imports(content: str) -> List[Dict[str, Any]]:
    """Extract import statements."""
    imports = []

    # ES6 imports
    import_pattern = r'import\s+(?:(\{[^}]+\}|\*\s+as\s+\w+|\w+)(?:\s*,\s*(\{[^}]+\}|\*\s+as\s+\w+))?\s+)?from\s+[\'"]([^\'"]+)[\'"]'
    for match in re.finditer(import_pattern, content):
        imports.append({
            "type": "es6",
            "imported": match.group(1) or match.group(2) or "",
            "source": match.group(3),
            "line": content[:match.start()].count('\n') + 1
        })

    # CommonJS requires
    require_pattern = r'(?:const|let|var)\s+([^=]+)\s*=\s*require\([\'"]([^\'"]+)[\'"]\)'
    for match in re.finditer(require_pattern, content):
        imports.append({
            "type": "commonjs",
            "imported": match.group(1).strip(),
            "source": match.group(2),
            "line": content[:match.start()].count('\n') + 1
        })

    return imports


def _extract_exports(content: str) -> List[Dict[str, Any]]:
    """Extract export statements."""
    exports = []

    # Named exports
    export_pattern = r'export\s+(?:const|let|var|function|class|interface|type)\s+(\w+)'
    for match in re.finditer(export_pattern, content):
        exports.append({
            "type": "named",
            "name": match.group(1),
            "line": content[:match.start()].count('\n') + 1
        })

    # Default exports
    default_pattern = r'export\s+default\s+(\w+)'
    for match in re.finditer(default_pattern, content):
        exports.append({
            "type": "default",
            "name": match.group(1),
            "line": content[:match.start()].count('\n') + 1
        })

    return exports


def _extract_functions(content: str) -> List[Dict[str, Any]]:
    """Extract function definitions."""
    functions = []

    # Function declarations
    func_pattern = r'(?:export\s+)?(?:async\s+)?function\s+(\w+)\s*\([^)]*\)\s*(?::\s*[^{]+)?\s*\{'
    for match in re.finditer(func_pattern, content):
        functions.append({
            "type": "function",
            "name": match.group(1),
            "line": content[:match.start()].count('\n') + 1,
            "body": _extract_function_body(content, match.end() - 1)
        })

    # Arrow functions
    arrow_pattern = r'(?:const|let|var)\s+(\w+)\s*=\s*(?:async\s+)?\([^)]*\)\s*=>\s*'
    for match in re.finditer(arrow_pattern, content):
        functions.append({
            "type": "arrow",
            "name": match.group(1),
            "line": content[:match.start()].count('\n') + 1,
            "body": ""  # More complex to extract for arrow functions
        })

    return functions


def _extract_classes(content: str) -> List[Dict[str, Any]]:
    """Extract class definitions."""
    classes = []

    class_pattern = r'(?:export\s+)?(?:abstract\s+)?class\s+(\w+)(?:\s+extends\s+\w+)?(?:\s+implements\s+[\w,\s]+)?\s*\{'
    for match in re.finditer(class_pattern, content):
        classes.append({
            "name": match.group(1),
            "line": content[:match.start()].count('\n') + 1
        })

    return classes


def _extract_function_body(content: str, start_pos: int) -> str:
    """Extract function body content."""
    brace_count = 1
    i = start_pos + 1

    while i < len(content) and brace_count > 0:
        if content[i] == '{':
            brace_count += 1
        elif content[i] == '}':
            brace_count -= 1
        i += 1

    return content[start_pos + 1:i - 1] if brace_count == 0 else ""


async def _run_typescript_check(content: str, file_path: str) -> Optional[Dict[str, Any]]:
    """Run TypeScript compiler check if available."""
    try:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ts', delete=False) as tmp_file:
            tmp_file.write(content)
            tmp_file.flush()

            # Try to run tsc --noEmit
            result = subprocess.run(
                ['npx', 'tsc', '--noEmit', '--target', 'ES2022', tmp_file.name],
                capture_output=True,
                text=True,
                timeout=30
            )

            Path(tmp_file.name).unlink()  # Clean up

            if result.returncode == 0:
                return {"errors": []}
            else:
                errors = result.stderr.strip().split('\n') if result.stderr else []
                return {"errors": errors}

    except Exception:
        return None


async def _run_eslint(file_path: str) -> Optional[Dict[str, Any]]:
    """Run ESLint if available."""
    try:
        result = subprocess.run(
            ['npx', 'eslint', '--format', 'json', file_path],
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.stdout:
            eslint_output = json.loads(result.stdout)
            return {
                "issues": eslint_output[0].get("messages", []) if eslint_output else [],
                "error_count": eslint_output[0].get("errorCount", 0) if eslint_output else 0,
                "warning_count": eslint_output[0].get("warningCount", 0) if eslint_output else 0
            }
    except Exception:
        pass

    return None


async def _analyze_eslint_patterns(content: str, file_path: str) -> Dict[str, Any]:
    """Manual analysis of common ESLint patterns."""
    issues = []

    lines = content.split('\n')

    for i, line in enumerate(lines, 1):
        # Check for common issues
        if re.search(r'\bvar\b', line):
            issues.append({
                "line": i,
                "column": line.find('var') + 1,
                "message": "Unexpected var, use let or const instead",
                "severity": 2,
                "ruleId": "no-var"
            })

        if '==' in line and '===' not in line:
            issues.append({
                "line": i,
                "column": line.find('==') + 1,
                "message": "Expected '===' and instead saw '=='",
                "severity": 2,
                "ruleId": "eqeqeq"
            })

        if re.search(r'console\.(log|warn|error)', line):
            issues.append({
                "line": i,
                "column": line.find('console') + 1,
                "message": "Unexpected console statement",
                "severity": 1,
                "ruleId": "no-console"
            })

    return {
        "issues": issues,
        "error_count": sum(1 for issue in issues if issue["severity"] == 2),
        "warning_count": sum(1 for issue in issues if issue["severity"] == 1)
    }


async def _generate_eslint_fixes(issues: List[Dict], file_path: str) -> List[Dict[str, Any]]:
    """Generate fix suggestions for ESLint issues."""
    suggestions = []

    for issue in issues:
        fix_suggestion = {
            "line": issue.get("line", 0),
            "rule": issue.get("ruleId", "unknown"),
            "message": issue.get("message", ""),
            "suggestion": ""
        }

        rule_id = issue.get("ruleId", "")

        if rule_id == "no-var":
            fix_suggestion["suggestion"] = "Replace 'var' with 'const' or 'let'"
        elif rule_id == "eqeqeq":
            fix_suggestion["suggestion"] = "Use '===' instead of '=='"
        elif rule_id == "no-console":
            fix_suggestion["suggestion"] = "Remove console statement or use a proper logging library"
        else:
            fix_suggestion["suggestion"] = "Check ESLint documentation for this rule"

        suggestions.append(fix_suggestion)

    return suggestions


async def _analyze_refactoring_opportunities(content: str, file_path: str, focus: str) -> List[Dict[str, Any]]:
    """Analyze code for refactoring opportunities."""
    opportunities = []

    lines = content.split('\n')
    functions = _extract_functions(content)

    # Long function detection
    for func in functions:
        if len(func.get("body", "").split('\n')) > 50:
            opportunities.append({
                "type": "long_function",
                "severity": "medium",
                "line": func.get("line", 0),
                "message": f"Function '{func['name']}' is too long (>50 lines)",
                "suggestion": "Consider breaking this function into smaller, more focused functions"
            })

    # Code duplication detection (simple)
    line_counts = {}
    for i, line in enumerate(lines):
        stripped = line.strip()
        if len(stripped) > 10 and not stripped.startswith('//'):
            if stripped in line_counts:
                line_counts[stripped].append(i + 1)
            else:
                line_counts[stripped] = [i + 1]

    for line_content, line_numbers in line_counts.items():
        if len(line_numbers) > 2:
            opportunities.append({
                "type": "code_duplication",
                "severity": "low",
                "lines": line_numbers,
                "message": f"Duplicated code found on lines: {', '.join(map(str, line_numbers))}",
                "suggestion": "Consider extracting common code into a function or variable"
            })

    # Magic numbers
    magic_number_pattern = r'\b(?<![\w.])\d+(?![\w.])\b'
    for i, line in enumerate(lines, 1):
        matches = re.finditer(magic_number_pattern, line)
        for match in matches:
            number = match.group()
            if number not in ['0', '1', '2']:  # Common acceptable numbers
                opportunities.append({
                    "type": "magic_number",
                    "severity": "low",
                    "line": i,
                    "column": match.start() + 1,
                    "message": f"Magic number '{number}' should be replaced with a named constant",
                    "suggestion": f"Consider defining a constant: const SOME_MEANINGFUL_NAME = {number};"
                })

    return opportunities


def _calculate_overall_score(complexity: Dict, types: Dict, imports: Dict) -> int:
    """Calculate an overall code quality score."""
    score = 100

    # Complexity penalties
    if complexity.get("cyclomatic_complexity", 0) > 20:
        score -= 20
    elif complexity.get("cyclomatic_complexity", 0) > 10:
        score -= 10

    # Type safety score (for TypeScript files)
    if "type_safety_score" in types:
        type_score = types["type_safety_score"]
        score = (score + type_score) // 2

    # Import organization
    if imports.get("total_imports", 0) > 20:
        score -= 5

    return max(0, min(100, score))


def _format_analysis_results(analysis: Dict[str, Any], analysis_type: str) -> str:
    """Format analysis results for display."""
    output = []

    if analysis_type == "full":
        output.append("🔍 **TypeScript/JavaScript Analysis Report**\n")

        # Syntax info
        syntax = analysis.get("syntax", {})
        output.append(f"📄 **File Information:**")
        output.append(f"- Lines: {syntax.get('line_count', 0)}")
        output.append(f"- Characters: {syntax.get('character_count', 0)}")
        output.append(f"- Type: {'TypeScript' if syntax.get('is_typescript') else 'JavaScript'}")
        output.append("")

        # Complexity
        complexity = analysis.get("complexity", {})
        output.append(f"📊 **Complexity Metrics:**")
        output.append(f"- Cyclomatic Complexity: {complexity.get('cyclomatic_complexity', 0)}")
        output.append(f"- Functions: {complexity.get('function_count', 0)}")
        output.append(f"- Max Function Complexity: {complexity.get('max_function_complexity', 0)}")
        output.append("")

        # Types (if TypeScript)
        types = analysis.get("types", {})
        if "type_safety_score" in types:
            output.append(f"🔒 **Type Safety:**")
            output.append(f"- Type Safety Score: {types.get('type_safety_score', 0)}/100")
            output.append(f"- Any Usage: {types.get('any_usage', 0)}")
            output.append(f"- Interfaces: {types.get('interfaces', 0)}")
            output.append("")

        # Overall score
        score = analysis.get("overall_score", 0)
        output.append(f"⭐ **Overall Score: {score}/100**")

    else:
        output.append(f"📋 **{analysis_type.title()} Analysis:**")
        output.append(json.dumps(analysis, indent=2))

    return '\n'.join(output)


def _format_eslint_results(result: Dict[str, Any], suggestions: List[Dict], fix_suggestions: bool) -> str:
    """Format ESLint results for display."""
    output = []

    output.append("🔧 **ESLint Analysis Report**\n")

    error_count = result.get("error_count", 0)
    warning_count = result.get("warning_count", 0)
    issues = result.get("issues", [])

    output.append(f"📊 **Summary:**")
    output.append(f"- Errors: {error_count}")
    output.append(f"- Warnings: {warning_count}")
    output.append(f"- Total Issues: {len(issues)}")
    output.append("")

    if issues:
        output.append("🚨 **Issues Found:**")
        for issue in issues[:10]:  # Limit to first 10 issues
            severity = "❌ ERROR" if issue.get("severity") == 2 else "⚠️ WARNING"
            line = issue.get("line", "?")
            rule = issue.get("ruleId", "unknown")
            message = issue.get("message", "No message")

            output.append(f"{severity} Line {line}: {message} ({rule})")

        if len(issues) > 10:
            output.append(f"... and {len(issues) - 10} more issues")
        output.append("")

    if fix_suggestions and suggestions:
        output.append("💡 **Fix Suggestions:**")
        for suggestion in suggestions[:5]:  # Limit to first 5 suggestions
            line = suggestion.get("line", "?")
            fix = suggestion.get("suggestion", "No suggestion")
            output.append(f"Line {line}: {fix}")
        output.append("")

    return '\n'.join(output)


def _format_refactor_suggestions(suggestions: List[Dict[str, Any]], focus: str) -> str:
    """Format refactoring suggestions for display."""
    output = []

    output.append(f"🔄 **Refactoring Suggestions ({focus})**\n")

    if not suggestions:
        output.append("✅ No refactoring opportunities found!")
        return '\n'.join(output)

    # Group by type
    by_type = {}
    for suggestion in suggestions:
        stype = suggestion.get("type", "other")
        if stype not in by_type:
            by_type[stype] = []
        by_type[stype].append(suggestion)

    for suggestion_type, items in by_type.items():
        output.append(f"📝 **{suggestion_type.replace('_', ' ').title()}:**")

        for item in items[:5]:  # Limit to 5 per type
            severity_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(item.get("severity"), "⚪")
            line = item.get("line", "?")
            message = item.get("message", "No message")
            suggestion = item.get("suggestion", "No suggestion")

            output.append(f"{severity_icon} Line {line}: {message}")
            output.append(f"   💡 {suggestion}")
            output.append("")

        if len(items) > 5:
            output.append(f"   ... and {len(items) - 5} more items")
            output.append("")

    return '\n'.join(output)