"""
TypeScript Type System Tools

Advanced TypeScript type analysis, type safety checking, and type improvement suggestions.
"""

import json
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple


async def analyze_type_safety(file_path: str, strict_mode: bool = True) -> Dict[str, Any]:
    """
    Analyze TypeScript code for type safety and coverage.

    Args:
        file_path: Path to TypeScript file
        strict_mode: Whether to enforce strict type checking

    Returns:
        Dict with type safety analysis results
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

        if not path.suffix in ['.ts', '.tsx']:
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ Type analysis only available for TypeScript files: {file_path}"
                }],
                "success": False,
                "error": "not_typescript"
            }

        content = path.read_text(encoding='utf-8')

        # Perform comprehensive type analysis
        type_analysis = await _comprehensive_type_analysis(content, str(path), strict_mode)

        formatted_output = _format_type_safety_results(type_analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": type_analysis,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Type safety analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_type_improvements(code_snippet: str, context: str = "") -> Dict[str, Any]:
    """
    Suggest improvements to TypeScript type annotations.

    Args:
        code_snippet: Code snippet to analyze
        context: Additional context about the code

    Returns:
        Dict with type improvement suggestions
    """
    try:
        improvements = await _analyze_type_improvements(code_snippet, context)

        formatted_output = _format_type_improvements(improvements, code_snippet)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "improvements": improvements,
            "original_code": code_snippet
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Type improvement analysis failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def check_strict_mode(project_path: str) -> Dict[str, Any]:
    """
    Check TypeScript project strict mode configuration.

    Args:
        project_path: Path to project directory

    Returns:
        Dict with strict mode analysis
    """
    try:
        path = Path(project_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Project path not found: {project_path}"
                }],
                "success": False,
                "error": "path_not_found"
            }

        strict_analysis = await _analyze_strict_mode_config(str(path))

        formatted_output = _format_strict_mode_results(strict_analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": strict_analysis,
            "project_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Strict mode check failed for {project_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

async def _comprehensive_type_analysis(content: str, file_path: str, strict_mode: bool) -> Dict[str, Any]:
    """Perform comprehensive TypeScript type analysis."""

    # Basic type metrics
    type_metrics = _analyze_type_metrics(content)

    # Type safety issues
    type_issues = _analyze_type_issues(content)

    # Generic usage
    generic_analysis = _analyze_generic_usage(content)

    # Type definitions
    type_definitions = _analyze_type_definitions(content)

    # Run TypeScript compiler check
    compiler_check = await _run_typescript_compiler(content, file_path, strict_mode)

    return {
        "metrics": type_metrics,
        "issues": type_issues,
        "generics": generic_analysis,
        "definitions": type_definitions,
        "compiler": compiler_check,
        "overall_score": _calculate_type_safety_score(type_metrics, type_issues)
    }


def _analyze_type_metrics(content: str) -> Dict[str, Any]:
    """Analyze basic type metrics."""
    lines = content.split('\n')

    # Count different type annotations
    explicit_types = len(re.findall(r':\s*[A-Za-z_]\w*(?:\[\]|\<[^>]+\>)?', content))
    any_usage = len(re.findall(r':\s*any\b', content))
    unknown_usage = len(re.findall(r':\s*unknown\b', content))
    never_usage = len(re.findall(r':\s*never\b', content))

    # Function return types
    function_return_types = len(re.findall(r'\)\s*:\s*[A-Za-z_]\w*', content))

    # Variable declarations
    const_declarations = len(re.findall(r'\bconst\s+\w+', content))
    let_declarations = len(re.findall(r'\blet\s+\w+', content))
    var_declarations = len(re.findall(r'\bvar\s+\w+', content))

    # Type assertions
    as_assertions = len(re.findall(r'\bas\s+\w+', content))
    angle_assertions = len(re.findall(r'<\w+>', content))

    return {
        "explicit_types": explicit_types,
        "any_usage": any_usage,
        "unknown_usage": unknown_usage,
        "never_usage": never_usage,
        "function_return_types": function_return_types,
        "const_declarations": const_declarations,
        "let_declarations": let_declarations,
        "var_declarations": var_declarations,
        "type_assertions": as_assertions + angle_assertions,
        "total_lines": len(lines)
    }


def _analyze_type_issues(content: str) -> List[Dict[str, Any]]:
    """Analyze potential type safety issues."""
    issues = []
    lines = content.split('\n')

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Any usage
        any_matches = re.finditer(r'\bany\b', stripped)
        for match in any_matches:
            issues.append({
                "type": "any_usage",
                "line": i,
                "column": match.start() + 1,
                "severity": "high",
                "message": "Usage of 'any' type reduces type safety",
                "suggestion": "Consider using a more specific type or 'unknown'"
            })

        # Type assertions
        assertion_matches = re.finditer(r'\bas\s+(\w+)', stripped)
        for match in assertion_matches:
            issues.append({
                "type": "type_assertion",
                "line": i,
                "column": match.start() + 1,
                "severity": "medium",
                "message": f"Type assertion to '{match.group(1)}' may be unsafe",
                "suggestion": "Verify this assertion is correct and consider using type guards"
            })

        # Implicit any (function parameters without types)
        implicit_any_matches = re.finditer(r'function\s+\w+\s*\(\s*(\w+)(?:\s*,\s*\w+)*\s*\)', stripped)
        for match in implicit_any_matches:
            issues.append({
                "type": "implicit_any",
                "line": i,
                "column": match.start() + 1,
                "severity": "medium",
                "message": "Function parameters have implicit 'any' type",
                "suggestion": "Add explicit type annotations to function parameters"
            })

        # Non-null assertions
        non_null_matches = re.finditer(r'!\.|\!\s*;', stripped)
        for match in non_null_matches:
            issues.append({
                "type": "non_null_assertion",
                "line": i,
                "column": match.start() + 1,
                "severity": "medium",
                "message": "Non-null assertion operator may hide potential runtime errors",
                "suggestion": "Consider using optional chaining or proper null checks"
            })

    return issues


def _analyze_generic_usage(content: str) -> Dict[str, Any]:
    """Analyze generic type usage."""

    # Generic function/class definitions
    generic_definitions = re.findall(r'<([A-Z]\w*(?:\s+extends\s+\w+)?(?:\s*,\s*[A-Z]\w*(?:\s+extends\s+\w+)?)*)>', content)

    # Generic constraints
    constraints = re.findall(r'<\s*([A-Z]\w*)\s+extends\s+(\w+)', content)

    # Utility type usage
    utility_types = {
        "Partial": len(re.findall(r'\bPartial<', content)),
        "Required": len(re.findall(r'\bRequired<', content)),
        "Pick": len(re.findall(r'\bPick<', content)),
        "Omit": len(re.findall(r'\bOmit<', content)),
        "Record": len(re.findall(r'\bRecord<', content)),
        "Exclude": len(re.findall(r'\bExclude<', content)),
        "Extract": len(re.findall(r'\bExtract<', content)),
        "ReturnType": len(re.findall(r'\bReturnType<', content)),
        "Parameters": len(re.findall(r'\bParameters<', content))
    }

    # Conditional types
    conditional_types = len(re.findall(r'\w+\s+extends\s+\w+\s*\?\s*\w+\s*:\s*\w+', content))

    # Mapped types
    mapped_types = len(re.findall(r'\{\s*\[.*in.*\]:', content))

    return {
        "generic_definitions": len(generic_definitions),
        "constraints": len(constraints),
        "utility_types": utility_types,
        "utility_type_total": sum(utility_types.values()),
        "conditional_types": conditional_types,
        "mapped_types": mapped_types,
        "complexity_score": _calculate_generic_complexity(
            len(generic_definitions),
            sum(utility_types.values()),
            conditional_types,
            mapped_types
        )
    }


def _analyze_type_definitions(content: str) -> Dict[str, Any]:
    """Analyze type definitions and interfaces."""

    # Interfaces
    interfaces = re.findall(r'interface\s+(\w+)(?:\s+extends\s+[\w,\s]+)?\s*\{', content)

    # Type aliases
    type_aliases = re.findall(r'type\s+(\w+)(?:<[^>]+>)?\s*=', content)

    # Enums
    enums = re.findall(r'enum\s+(\w+)\s*\{', content)

    # Classes
    classes = re.findall(r'class\s+(\w+)(?:\s+extends\s+\w+)?(?:\s+implements\s+[\w,\s]+)?\s*\{', content)

    return {
        "interfaces": {
            "count": len(interfaces),
            "names": interfaces
        },
        "type_aliases": {
            "count": len(type_aliases),
            "names": type_aliases
        },
        "enums": {
            "count": len(enums),
            "names": enums
        },
        "classes": {
            "count": len(classes),
            "names": classes
        },
        "total_definitions": len(interfaces) + len(type_aliases) + len(enums) + len(classes)
    }


async def _run_typescript_compiler(content: str, file_path: str, strict_mode: bool) -> Dict[str, Any]:
    """Run TypeScript compiler for detailed analysis."""
    try:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ts', delete=False) as tmp_file:
            tmp_file.write(content)
            tmp_file.flush()

            # Create temporary tsconfig
            tsconfig = {
                "compilerOptions": {
                    "target": "ES2022",
                    "module": "ESNext",
                    "strict": strict_mode,
                    "noEmit": True,
                    "skipLibCheck": True
                },
                "files": [tmp_file.name]
            }

            with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as config_file:
                json.dump(tsconfig, config_file)
                config_file.flush()

                # Run TypeScript compiler
                result = subprocess.run(
                    ['npx', 'tsc', '--project', config_file.name],
                    capture_output=True,
                    text=True,
                    timeout=30
                )

                Path(tmp_file.name).unlink()
                Path(config_file.name).unlink()

                return {
                    "success": result.returncode == 0,
                    "errors": result.stderr.strip().split('\n') if result.stderr else [],
                    "warnings": [],
                    "exit_code": result.returncode
                }

    except Exception as e:
        return {
            "success": False,
            "errors": [f"Compiler check failed: {str(e)}"],
            "warnings": [],
            "exit_code": -1
        }


async def _analyze_type_improvements(code_snippet: str, context: str) -> List[Dict[str, Any]]:
    """Analyze code for type improvement opportunities."""
    improvements = []

    lines = code_snippet.split('\n')

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Suggest explicit return types for functions
        func_without_return_type = re.search(r'function\s+\w+\s*\([^)]*\)\s*\{', stripped)
        if func_without_return_type:
            improvements.append({
                "type": "explicit_return_type",
                "line": i,
                "severity": "low",
                "message": "Function missing explicit return type",
                "suggestion": "Add explicit return type annotation",
                "example": "function myFunction(): ReturnType { ... }"
            })

        # Suggest replacing any with specific types
        any_usage = re.search(r':\s*any\b', stripped)
        if any_usage:
            improvements.append({
                "type": "replace_any",
                "line": i,
                "severity": "high",
                "message": "Replace 'any' with specific type",
                "suggestion": "Use a more specific type or 'unknown' with type guards",
                "example": "const value: string | number = ..."
            })

        # Suggest union types for multiple conditions
        if_conditions = re.findall(r'if\s*\(\s*(\w+)\s*===\s*[\'"](\w+)[\'"]', stripped)
        if len(if_conditions) > 1:
            improvements.append({
                "type": "union_type",
                "line": i,
                "severity": "medium",
                "message": "Consider using union types for multiple string comparisons",
                "suggestion": "Define a union type for the possible values",
                "example": "type Status = 'pending' | 'complete' | 'error';"
            })

        # Suggest generic types for arrays
        array_without_type = re.search(r':\s*\[\]', stripped)
        if array_without_type:
            improvements.append({
                "type": "generic_array",
                "line": i,
                "severity": "medium",
                "message": "Array missing element type",
                "suggestion": "Specify the array element type",
                "example": "const items: string[] = [];"
            })

        # Suggest optional properties
        if_property_check = re.search(r'if\s*\(\s*(\w+)\.(\w+)\s*\)', stripped)
        if if_property_check:
            improvements.append({
                "type": "optional_property",
                "line": i,
                "severity": "low",
                "message": "Consider making property optional in type definition",
                "suggestion": "Use optional property syntax in interface",
                "example": f"interface MyType {{ {if_property_check.group(2)}?: string; }}"
            })

    return improvements


async def _analyze_strict_mode_config(project_path: str) -> Dict[str, Any]:
    """Analyze TypeScript strict mode configuration."""
    path = Path(project_path)

    # Look for tsconfig.json files
    tsconfig_files = list(path.glob('**/tsconfig*.json'))

    analysis = {
        "tsconfig_files": [],
        "strict_settings": {},
        "recommendations": []
    }

    for config_file in tsconfig_files:
        try:
            config_content = json.loads(config_file.read_text())
            compiler_options = config_content.get("compilerOptions", {})

            file_analysis = {
                "file": str(config_file.relative_to(path)),
                "strict_mode": compiler_options.get("strict", False),
                "individual_checks": {
                    "noImplicitAny": compiler_options.get("noImplicitAny", False),
                    "strictNullChecks": compiler_options.get("strictNullChecks", False),
                    "strictFunctionTypes": compiler_options.get("strictFunctionTypes", False),
                    "strictBindCallApply": compiler_options.get("strictBindCallApply", False),
                    "strictPropertyInitialization": compiler_options.get("strictPropertyInitialization", False),
                    "noImplicitReturns": compiler_options.get("noImplicitReturns", False),
                    "noImplicitThis": compiler_options.get("noImplicitThis", False),
                    "alwaysStrict": compiler_options.get("alwaysStrict", False)
                },
                "additional_checks": {
                    "noUncheckedIndexedAccess": compiler_options.get("noUncheckedIndexedAccess", False),
                    "exactOptionalPropertyTypes": compiler_options.get("exactOptionalPropertyTypes", False),
                    "noImplicitOverride": compiler_options.get("noImplicitOverride", False)
                }
            }

            analysis["tsconfig_files"].append(file_analysis)

        except Exception as e:
            analysis["tsconfig_files"].append({
                "file": str(config_file.relative_to(path)),
                "error": f"Failed to parse: {str(e)}"
            })

    # Generate recommendations
    analysis["recommendations"] = _generate_strict_mode_recommendations(analysis["tsconfig_files"])

    return analysis


def _generate_strict_mode_recommendations(configs: List[Dict]) -> List[Dict[str, Any]]:
    """Generate recommendations for strict mode configuration."""
    recommendations = []

    for config in configs:
        if "error" in config:
            continue

        file_name = config["file"]

        if not config["strict_mode"]:
            recommendations.append({
                "type": "enable_strict",
                "file": file_name,
                "severity": "high",
                "message": "Enable strict mode for better type safety",
                "suggestion": 'Set "strict": true in compilerOptions'
            })

        individual_checks = config.get("individual_checks", {})
        for check, enabled in individual_checks.items():
            if not enabled and config["strict_mode"]:
                # These should be enabled by strict mode
                continue
            elif not enabled:
                recommendations.append({
                    "type": "individual_check",
                    "file": file_name,
                    "severity": "medium",
                    "message": f"Consider enabling {check}",
                    "suggestion": f'Set "{check}": true in compilerOptions'
                })

        additional_checks = config.get("additional_checks", {})
        for check, enabled in additional_checks.items():
            if not enabled:
                recommendations.append({
                    "type": "additional_check",
                    "file": file_name,
                    "severity": "low",
                    "message": f"Consider enabling {check} for even stricter type checking",
                    "suggestion": f'Set "{check}": true in compilerOptions'
                })

    return recommendations


def _calculate_type_safety_score(metrics: Dict, issues: List[Dict]) -> int:
    """Calculate a type safety score based on metrics and issues."""
    base_score = 100

    # Penalize any usage
    any_penalty = min(metrics["any_usage"] * 5, 30)
    base_score -= any_penalty

    # Penalize issues
    for issue in issues:
        if issue["severity"] == "high":
            base_score -= 10
        elif issue["severity"] == "medium":
            base_score -= 5
        else:
            base_score -= 2

    # Bonus for explicit types
    if metrics["explicit_types"] > 0:
        type_ratio = metrics["explicit_types"] / max(metrics["total_lines"], 1)
        bonus = min(int(type_ratio * 20), 15)
        base_score += bonus

    return max(0, min(100, base_score))


def _calculate_generic_complexity(definitions: int, utility_types: int, conditional: int, mapped: int) -> int:
    """Calculate generic type complexity score."""
    return definitions * 2 + utility_types + conditional * 3 + mapped * 4


def _format_type_safety_results(analysis: Dict[str, Any]) -> str:
    """Format type safety analysis results."""
    output = []

    output.append("🔒 **TypeScript Type Safety Analysis**\n")

    # Overall score
    overall_score = analysis.get("overall_score", 0)
    score_emoji = "🟢" if overall_score >= 80 else "🟡" if overall_score >= 60 else "🔴"
    output.append(f"{score_emoji} **Overall Type Safety Score: {overall_score}/100**\n")

    # Metrics
    metrics = analysis.get("metrics", {})
    output.append("📊 **Type Metrics:**")
    output.append(f"- Explicit types: {metrics.get('explicit_types', 0)}")
    output.append(f"- Any usage: {metrics.get('any_usage', 0)} ⚠️")
    output.append(f"- Function return types: {metrics.get('function_return_types', 0)}")
    output.append(f"- Type assertions: {metrics.get('type_assertions', 0)}")
    output.append("")

    # Issues
    issues = analysis.get("issues", [])
    if issues:
        output.append("🚨 **Type Safety Issues:**")
        for issue in issues[:10]:  # Limit to first 10 issues
            severity_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(issue["severity"], "⚪")
            line = issue["line"]
            message = issue["message"]
            output.append(f"{severity_icon} Line {line}: {message}")

        if len(issues) > 10:
            output.append(f"... and {len(issues) - 10} more issues")
        output.append("")

    # Generic usage
    generics = analysis.get("generics", {})
    if generics.get("generic_definitions", 0) > 0 or generics.get("utility_type_total", 0) > 0:
        output.append("🔧 **Generic Type Usage:**")
        output.append(f"- Generic definitions: {generics.get('generic_definitions', 0)}")
        output.append(f"- Utility types: {generics.get('utility_type_total', 0)}")
        output.append(f"- Conditional types: {generics.get('conditional_types', 0)}")
        output.append(f"- Complexity score: {generics.get('complexity_score', 0)}")
        output.append("")

    # Compiler check
    compiler = analysis.get("compiler", {})
    if compiler.get("errors"):
        output.append("⚡ **TypeScript Compiler Issues:**")
        for error in compiler["errors"][:5]:
            output.append(f"❌ {error}")
        output.append("")

    return '\n'.join(output)


def _format_type_improvements(improvements: List[Dict], code_snippet: str) -> str:
    """Format type improvement suggestions."""
    output = []

    output.append("💡 **Type Improvement Suggestions**\n")

    if not improvements:
        output.append("✅ No type improvements needed!")
        return '\n'.join(output)

    # Group by type
    by_type = {}
    for improvement in improvements:
        imp_type = improvement.get("type", "other")
        if imp_type not in by_type:
            by_type[imp_type] = []
        by_type[imp_type].append(improvement)

    for improvement_type, items in by_type.items():
        type_name = improvement_type.replace('_', ' ').title()
        output.append(f"📝 **{type_name}:**")

        for item in items:
            severity_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(item.get("severity"), "⚪")
            line = item.get("line", "?")
            message = item.get("message", "No message")
            suggestion = item.get("suggestion", "No suggestion")
            example = item.get("example", "")

            output.append(f"{severity_icon} Line {line}: {message}")
            output.append(f"   💡 {suggestion}")
            if example:
                output.append(f"   📄 Example: `{example}`")
            output.append("")

    return '\n'.join(output)


def _format_strict_mode_results(analysis: Dict[str, Any]) -> str:
    """Format strict mode analysis results."""
    output = []

    output.append("⚙️ **TypeScript Strict Mode Analysis**\n")

    configs = analysis.get("tsconfig_files", [])

    if not configs:
        output.append("❌ No tsconfig.json files found")
        return '\n'.join(output)

    output.append("📄 **Configuration Files:**")
    for config in configs:
        if "error" in config:
            output.append(f"❌ {config['file']}: {config['error']}")
            continue

        file_name = config["file"]
        strict_enabled = config["strict_mode"]
        status = "✅ Enabled" if strict_enabled else "❌ Disabled"

        output.append(f"📁 {file_name}: Strict Mode {status}")

        if strict_enabled:
            # Show additional checks
            additional = config.get("additional_checks", {})
            enabled_additional = [k for k, v in additional.items() if v]
            if enabled_additional:
                output.append(f"   🔧 Additional checks: {', '.join(enabled_additional)}")

        output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            severity_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("severity"), "⚪")
            file_name = rec.get("file", "")
            message = rec.get("message", "")
            suggestion = rec.get("suggestion", "")

            output.append(f"{severity_icon} {file_name}: {message}")
            output.append(f"   💡 {suggestion}")
            output.append("")
    else:
        output.append("✅ Configuration looks good!")

    return '\n'.join(output)