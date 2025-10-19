"""
Rust Code Analysis Tools

Core functionality for analyzing Rust code quality, patterns, and structure
with focus on Rust-specific idioms and best practices.
"""

import re
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, Any, List, Optional


async def analyze_rust_code(file_path: str, analysis_type: str = "full") -> Dict[str, Any]:
    """
    Analyze Rust code for various quality metrics and patterns.

    Args:
        file_path: Path to Rust file to analyze
        analysis_type: Type of analysis (full, syntax, structure, patterns)

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

        if not path.suffix == '.rs':
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ Not a Rust file: {file_path}"
                }],
                "success": False,
                "error": "not_rust_file"
            }

        content = path.read_text(encoding='utf-8')

        if analysis_type == "syntax":
            analysis = _analyze_syntax(content, str(path))
        elif analysis_type == "structure":
            analysis = _analyze_structure(content)
        elif analysis_type == "patterns":
            analysis = _analyze_patterns(content)
        else:  # full
            analysis = await _analyze_full_rust(content, str(path))

        return {
            "content": [{
                "type": "text",
                "text": _format_rust_analysis_results(analysis, analysis_type)
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


async def check_clippy_warnings(file_path: str, fix_suggestions: bool = True) -> Dict[str, Any]:
    """
    Check Rust code against Clippy linting rules.

    Args:
        file_path: Path to Rust file
        fix_suggestions: Whether to include fix suggestions

    Returns:
        Dict with Clippy analysis results
    """
    try:
        path = Path(file_path)

        if not path.exists() or path.suffix != '.rs':
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Invalid Rust file: {file_path}"
                }],
                "success": False,
                "error": "invalid_file"
            }

        # Try to run Clippy if available
        clippy_result = await _run_clippy(str(path))

        if clippy_result is None:
            # Fallback to manual analysis
            content = path.read_text(encoding='utf-8')
            clippy_result = _analyze_clippy_patterns(content, str(path))

        suggestions = []
        if fix_suggestions and clippy_result.get("warnings"):
            suggestions = _generate_clippy_fixes(clippy_result["warnings"], str(path))

        formatted_output = _format_clippy_results(clippy_result, suggestions, fix_suggestions)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "clippy_result": clippy_result,
            "suggestions": suggestions,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Clippy check failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_refactors(file_path: str, focus: str = "all") -> Dict[str, Any]:
    """
    Suggest refactoring opportunities for Rust code.

    Args:
        file_path: Path to Rust file
        focus: Focus area (all, performance, readability, ownership, async)

    Returns:
        Dict with refactoring suggestions
    """
    try:
        path = Path(file_path)

        if not path.exists() or path.suffix != '.rs':
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Invalid Rust file: {file_path}"
                }],
                "success": False,
                "error": "invalid_file"
            }

        content = path.read_text(encoding='utf-8')

        refactor_suggestions = await _analyze_rust_refactoring_opportunities(content, str(path), focus)

        formatted_output = _format_rust_refactor_suggestions(refactor_suggestions, focus)

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

def _analyze_syntax(content: str, file_path: str) -> Dict[str, Any]:
    """Analyze basic Rust syntax and structure."""
    lines = content.split('\n')

    return {
        "line_count": len(lines),
        "character_count": len(content),
        "has_main_function": "fn main()" in content,
        "imports": _extract_rust_imports(content),
        "exports": _extract_rust_exports(content),
        "functions": _extract_rust_functions(content),
        "structs": _extract_rust_structs(content),
        "enums": _extract_rust_enums(content),
        "traits": _extract_rust_traits(content),
        "impls": _extract_rust_impls(content),
        "macros": _extract_rust_macros(content)
    }


def _analyze_structure(content: str) -> Dict[str, Any]:
    """Analyze Rust code structure and organization."""
    lines = content.split('\n')
    non_empty_lines = [line.strip() for line in lines if line.strip() and not line.strip().startswith('//')]

    return {
        "code_lines": len(non_empty_lines),
        "comment_lines": len([line for line in lines if line.strip().startswith('//')]),
        "doc_comments": len(re.findall(r'///|//!', content)),
        "modules": len(re.findall(r'^mod\s+\w+', content, re.MULTILINE)),
        "public_items": len(re.findall(r'^pub\s+', content, re.MULTILINE)),
        "private_items": _count_private_items(content),
        "unsafe_blocks": len(re.findall(r'unsafe\s*\{', content)),
        "test_functions": len(re.findall(r'#\[test\]', content))
    }


def _analyze_patterns(content: str) -> Dict[str, Any]:
    """Analyze Rust-specific patterns and idioms."""
    return {
        "error_handling": _analyze_error_handling_patterns(content),
        "ownership_patterns": _analyze_ownership_patterns(content),
        "iterator_usage": _analyze_iterator_patterns(content),
        "match_expressions": len(re.findall(r'match\s+', content)),
        "if_let_patterns": len(re.findall(r'if\s+let\s+', content)),
        "while_let_patterns": len(re.findall(r'while\s+let\s+', content)),
        "closure_usage": len(re.findall(r'\|[^|]*\|\s*[^;]*', content)),
        "lifetime_annotations": len(re.findall(r"'[a-z]+", content))
    }


async def _analyze_full_rust(content: str, file_path: str) -> Dict[str, Any]:
    """Perform comprehensive Rust analysis."""
    syntax = _analyze_syntax(content, file_path)
    structure = _analyze_structure(content)
    patterns = _analyze_patterns(content)

    # Additional full analysis
    complexity = _analyze_complexity(content)
    quality = _analyze_code_quality(content)

    return {
        "syntax": syntax,
        "structure": structure,
        "patterns": patterns,
        "complexity": complexity,
        "quality": quality,
        "overall_score": _calculate_rust_score(structure, patterns, complexity, quality)
    }


def _extract_rust_imports(content: str) -> List[Dict[str, Any]]:
    """Extract Rust use statements."""
    imports = []

    use_pattern = r'use\s+([^;]+);'
    for match in re.finditer(use_pattern, content):
        use_path = match.group(1).strip()
        imports.append({
            "path": use_path,
            "line": content[:match.start()].count('\n') + 1,
            "is_external": not use_path.startswith('crate::') and not use_path.startswith('super::') and not use_path.startswith('self::'),
            "is_std": use_path.startswith('std::')
        })

    return imports


def _extract_rust_exports(content: str) -> List[Dict[str, Any]]:
    """Extract public Rust items."""
    exports = []

    pub_pattern = r'pub\s+(?:(fn|struct|enum|trait|type|const|static|mod)\s+(\w+))'
    for match in re.finditer(pub_pattern, content):
        item_type, name = match.groups()
        exports.append({
            "type": item_type,
            "name": name,
            "line": content[:match.start()].count('\n') + 1
        })

    return exports


def _extract_rust_functions(content: str) -> List[Dict[str, Any]]:
    """Extract Rust function definitions."""
    functions = []

    # Function pattern with optional async, pub, const
    func_pattern = r'(?:pub\s+)?(?:async\s+)?(?:const\s+)?fn\s+(\w+)\s*(?:<[^>]*>)?\s*\([^)]*\)(?:\s*->\s*[^{]+)?\s*\{'
    for match in re.finditer(func_pattern, content):
        name = match.group(1)
        is_async = 'async' in match.group(0)
        is_pub = 'pub' in match.group(0)
        is_const = 'const' in match.group(0)

        functions.append({
            "name": name,
            "line": content[:match.start()].count('\n') + 1,
            "is_async": is_async,
            "is_public": is_pub,
            "is_const": is_const,
            "is_main": name == "main"
        })

    return functions


def _extract_rust_structs(content: str) -> List[Dict[str, Any]]:
    """Extract Rust struct definitions."""
    structs = []

    struct_pattern = r'(?:pub\s+)?struct\s+(\w+)(?:<[^>]*>)?\s*(?:\([^)]*\)|\{[^}]*\}|;)'
    for match in re.finditer(struct_pattern, content):
        name = match.group(1)
        is_pub = 'pub' in match.group(0)
        is_tuple = '(' in match.group(0)
        is_unit = match.group(0).endswith(';')

        structs.append({
            "name": name,
            "line": content[:match.start()].count('\n') + 1,
            "is_public": is_pub,
            "is_tuple_struct": is_tuple,
            "is_unit_struct": is_unit
        })

    return structs


def _extract_rust_enums(content: str) -> List[Dict[str, Any]]:
    """Extract Rust enum definitions."""
    enums = []

    enum_pattern = r'(?:pub\s+)?enum\s+(\w+)(?:<[^>]*>)?\s*\{'
    for match in re.finditer(enum_pattern, content):
        name = match.group(1)
        is_pub = 'pub' in match.group(0)

        enums.append({
            "name": name,
            "line": content[:match.start()].count('\n') + 1,
            "is_public": is_pub
        })

    return enums


def _extract_rust_traits(content: str) -> List[Dict[str, Any]]:
    """Extract Rust trait definitions."""
    traits = []

    trait_pattern = r'(?:pub\s+)?trait\s+(\w+)(?:<[^>]*>)?(?:\s*:\s*[^{]+)?\s*\{'
    for match in re.finditer(trait_pattern, content):
        name = match.group(1)
        is_pub = 'pub' in match.group(0)

        traits.append({
            "name": name,
            "line": content[:match.start()].count('\n') + 1,
            "is_public": is_pub
        })

    return traits


def _extract_rust_impls(content: str) -> List[Dict[str, Any]]:
    """Extract Rust impl blocks."""
    impls = []

    impl_pattern = r'impl(?:<[^>]*>)?\s+(?:(\w+)\s+for\s+)?(\w+)(?:<[^>]*>)?\s*\{'
    for match in re.finditer(impl_pattern, content):
        trait_name = match.group(1)
        type_name = match.group(2)

        impls.append({
            "type_name": type_name,
            "trait_name": trait_name,
            "line": content[:match.start()].count('\n') + 1,
            "is_trait_impl": trait_name is not None
        })

    return impls


def _extract_rust_macros(content: str) -> List[Dict[str, Any]]:
    """Extract Rust macro definitions and invocations."""
    macros = []

    # Macro definitions
    macro_def_pattern = r'macro_rules!\s+(\w+)'
    for match in re.finditer(macro_def_pattern, content):
        name = match.group(1)
        macros.append({
            "name": name,
            "type": "definition",
            "line": content[:match.start()].count('\n') + 1
        })

    # Common macro invocations
    common_macros = ['println!', 'eprintln!', 'panic!', 'assert!', 'debug_assert!', 'vec!', 'format!']
    for macro_name in common_macros:
        pattern = rf'{macro_name}\s*\('
        for match in re.finditer(pattern, content):
            macros.append({
                "name": macro_name,
                "type": "invocation",
                "line": content[:match.start()].count('\n') + 1
            })

    return macros


def _count_private_items(content: str) -> int:
    """Count private items (items without pub keyword)."""
    # Count functions, structs, enums, traits that don't have pub
    patterns = [
        r'^(?!.*pub)\s*fn\s+\w+',
        r'^(?!.*pub)\s*struct\s+\w+',
        r'^(?!.*pub)\s*enum\s+\w+',
        r'^(?!.*pub)\s*trait\s+\w+'
    ]

    count = 0
    for pattern in patterns:
        count += len(re.findall(pattern, content, re.MULTILINE))

    return count


def _analyze_error_handling_patterns(content: str) -> Dict[str, Any]:
    """Analyze error handling patterns in Rust code."""
    return {
        "result_usage": len(re.findall(r'Result<[^>]+>', content)),
        "option_usage": len(re.findall(r'Option<[^>]+>', content)),
        "question_operator": len(re.findall(r'\?\s*[;}]', content)),
        "unwrap_calls": len(re.findall(r'\.unwrap\(\)', content)),
        "expect_calls": len(re.findall(r'\.expect\(', content)),
        "panic_calls": len(re.findall(r'panic!\s*\(', content)),
        "anyhow_usage": "anyhow::" in content or "use anyhow" in content,
        "thiserror_usage": "thiserror::" in content or "use thiserror" in content
    }


def _analyze_ownership_patterns(content: str) -> Dict[str, Any]:
    """Analyze ownership and borrowing patterns."""
    return {
        "mutable_borrows": len(re.findall(r'&mut\s+', content)),
        "immutable_borrows": len(re.findall(r'&(?!mut)\s*\w+', content)) - len(re.findall(r'&mut\s+', content)),
        "clone_calls": len(re.findall(r'\.clone\(\)', content)),
        "rc_usage": len(re.findall(r'Rc<[^>]+>', content)),
        "arc_usage": len(re.findall(r'Arc<[^>]+>', content)),
        "box_usage": len(re.findall(r'Box<[^>]+>', content)),
        "refcell_usage": len(re.findall(r'RefCell<[^>]+>', content)),
        "mutex_usage": len(re.findall(r'Mutex<[^>]+>', content))
    }


def _analyze_iterator_patterns(content: str) -> Dict[str, Any]:
    """Analyze iterator usage patterns."""
    return {
        "iter_calls": len(re.findall(r'\.iter\(\)', content)),
        "into_iter_calls": len(re.findall(r'\.into_iter\(\)', content)),
        "collect_calls": len(re.findall(r'\.collect\(\)', content)),
        "map_calls": len(re.findall(r'\.map\(', content)),
        "filter_calls": len(re.findall(r'\.filter\(', content)),
        "fold_calls": len(re.findall(r'\.fold\(', content)),
        "reduce_calls": len(re.findall(r'\.reduce\(', content))
    }


def _analyze_complexity(content: str) -> Dict[str, Any]:
    """Analyze code complexity metrics."""
    lines = content.split('\n')
    non_empty_lines = [line.strip() for line in lines if line.strip()]

    # Complexity indicators
    complexity_keywords = ['if', 'else', 'match', 'for', 'while', 'loop', '&&', '||', '?']
    complexity_score = 1  # Base complexity

    for line in non_empty_lines:
        for keyword in complexity_keywords:
            complexity_score += line.count(keyword)

    functions = _extract_rust_functions(content)
    function_complexities = []

    for func in functions:
        # Simple function complexity estimation
        func_name = func["name"]
        # Find function body (simplified)
        func_pattern = rf'fn\s+{func_name}\s*[^{{]*\{{'
        match = re.search(func_pattern, content)
        if match:
            # Estimate function complexity by counting keywords in vicinity
            start_pos = match.end()
            # Look for the function end (simplified - just take next 500 chars)
            func_body = content[start_pos:start_pos + 500]
            func_complexity = 1
            for keyword in complexity_keywords:
                func_complexity += func_body.count(keyword)

            function_complexities.append({
                "name": func_name,
                "complexity": min(func_complexity, 20),  # Cap at 20
                "line": func["line"]
            })

    return {
        "total_lines": len(lines),
        "code_lines": len(non_empty_lines),
        "cyclomatic_complexity": min(complexity_score, 50),  # Cap at 50
        "function_count": len(functions),
        "function_complexities": function_complexities,
        "max_function_complexity": max([f["complexity"] for f in function_complexities]) if function_complexities else 0
    }


def _analyze_code_quality(content: str) -> Dict[str, Any]:
    """Analyze general code quality indicators."""
    return {
        "documentation_ratio": _calculate_documentation_ratio(content),
        "test_coverage_indicators": _analyze_test_indicators(content),
        "naming_convention_score": _analyze_naming_conventions(content),
        "code_organization_score": _analyze_code_organization(content)
    }


def _calculate_documentation_ratio(content: str) -> float:
    """Calculate ratio of documented items."""
    lines = content.split('\n')
    doc_lines = len([line for line in lines if line.strip().startswith('///')])
    code_lines = len([line for line in lines if line.strip() and not line.strip().startswith('//')])

    return round(doc_lines / max(code_lines, 1), 3)


def _analyze_test_indicators(content: str) -> Dict[str, Any]:
    """Analyze indicators of test coverage."""
    return {
        "has_test_module": "#[cfg(test)]" in content,
        "test_functions": len(re.findall(r'#\[test\]', content)),
        "assert_usage": len(re.findall(r'assert[_!]', content)),
        "has_integration_tests": False  # Would need to check tests/ directory
    }


def _analyze_naming_conventions(content: str) -> int:
    """Analyze adherence to Rust naming conventions."""
    score = 100
    violations = []

    # Check function names (should be snake_case)
    functions = _extract_rust_functions(content)
    for func in functions:
        name = func["name"]
        if not re.match(r'^[a-z][a-z0-9_]*$', name) and name != "main":
            violations.append(f"Function name '{name}' should be snake_case")

    # Check struct names (should be PascalCase)
    structs = _extract_rust_structs(content)
    for struct in structs:
        name = struct["name"]
        if not re.match(r'^[A-Z][a-zA-Z0-9]*$', name):
            violations.append(f"Struct name '{name}' should be PascalCase")

    # Deduct points for violations
    score -= min(len(violations) * 10, 50)

    return max(score, 0)


def _analyze_code_organization(content: str) -> int:
    """Analyze code organization and structure."""
    score = 100

    lines = content.split('\n')
    if len(lines) > 300:
        score -= 10  # Long files are harder to maintain

    # Check for proper use of modules
    if "mod " not in content and len(lines) > 100:
        score -= 15  # Large files should be modularized

    # Check for proper imports organization
    imports = _extract_rust_imports(content)
    if len(imports) > 15:
        score -= 5  # Many imports suggest high coupling

    return max(score, 0)


def _calculate_rust_score(structure: Dict, patterns: Dict, complexity: Dict, quality: Dict) -> int:
    """Calculate overall Rust code quality score."""
    score = 100

    # Penalize complexity
    if complexity.get("cyclomatic_complexity", 0) > 20:
        score -= 20
    elif complexity.get("cyclomatic_complexity", 0) > 10:
        score -= 10

    # Penalize unsafe code
    if structure.get("unsafe_blocks", 0) > 3:
        score -= 15

    # Reward good error handling
    error_handling = patterns.get("error_handling", {})
    if error_handling.get("result_usage", 0) > error_handling.get("unwrap_calls", 0):
        score += 10

    # Reward documentation
    doc_ratio = quality.get("documentation_ratio", 0)
    if doc_ratio > 0.2:
        score += 10
    elif doc_ratio > 0.1:
        score += 5

    # Reward tests
    if quality.get("test_coverage_indicators", {}).get("has_test_module", False):
        score += 15

    # Apply naming and organization scores
    score = (score + quality.get("naming_convention_score", 100) + quality.get("code_organization_score", 100)) // 3

    return max(0, min(100, score))


async def _run_clippy(file_path: str) -> Optional[Dict[str, Any]]:
    """Run Clippy if available."""
    try:
        # Try to run clippy on the file
        result = subprocess.run(
            ['cargo', 'clippy', '--', '--json', file_path],
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode == 0:
            return {"warnings": [], "errors": []}
        else:
            # Parse clippy output (simplified)
            warnings = []
            errors = []

            # This is a simplified parser - real clippy output is JSON
            for line in result.stderr.strip().split('\n') if result.stderr else []:
                if 'warning:' in line:
                    warnings.append(line)
                elif 'error:' in line:
                    errors.append(line)

            return {
                "warnings": warnings[:10],  # Limit to 10
                "errors": errors[:10]
            }

    except Exception:
        return None


def _analyze_clippy_patterns(content: str, file_path: str) -> Dict[str, Any]:
    """Manual analysis of common Clippy patterns."""
    warnings = []
    errors = []

    lines = content.split('\n')

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Check for common Clippy warnings
        if '.unwrap()' in stripped:
            warnings.append(f"Line {i}: Consider using expect() instead of unwrap() for better error messages")

        if '.clone()' in stripped and '&' in stripped:
            warnings.append(f"Line {i}: Unnecessary clone, consider using references")

        if 'use std::mem::drop' in stripped:
            warnings.append(f"Line {i}: Unnecessary explicit drop import")

        if re.search(r'if\s+.*\s+==\s+true', stripped):
            warnings.append(f"Line {i}: Redundant boolean comparison")

        if 'Vec::new()' in stripped and 'mut' in stripped:
            warnings.append(f"Line {i}: Consider using Vec::with_capacity() if size is known")

    return {
        "warnings": warnings[:15],  # Limit warnings
        "errors": errors
    }


def _generate_clippy_fixes(warnings: List[str], file_path: str) -> List[Dict[str, Any]]:
    """Generate fix suggestions for Clippy warnings."""
    fixes = []

    for warning in warnings:
        fix = {
            "warning": warning,
            "suggestion": "",
            "confidence": "medium"
        }

        if "unwrap()" in warning:
            fix["suggestion"] = "Replace .unwrap() with .expect(\"meaningful error message\")"
            fix["confidence"] = "high"
        elif "clone()" in warning:
            fix["suggestion"] = "Consider using references instead of cloning"
            fix["confidence"] = "medium"
        elif "boolean comparison" in warning:
            fix["suggestion"] = "Remove redundant == true comparison"
            fix["confidence"] = "high"
        elif "with_capacity" in warning:
            fix["suggestion"] = "Use Vec::with_capacity(n) when size is known"
            fix["confidence"] = "medium"
        else:
            fix["suggestion"] = "Check Clippy documentation for this warning"
            fix["confidence"] = "low"

        fixes.append(fix)

    return fixes


async def _analyze_rust_refactoring_opportunities(content: str, file_path: str, focus: str) -> List[Dict[str, Any]]:
    """Analyze Rust code for refactoring opportunities."""
    opportunities = []

    if focus in ["all", "performance"]:
        opportunities.extend(_analyze_performance_opportunities(content))

    if focus in ["all", "ownership"]:
        opportunities.extend(_analyze_ownership_opportunities(content))

    if focus in ["all", "readability"]:
        opportunities.extend(_analyze_readability_opportunities(content))

    if focus in ["all", "async"]:
        opportunities.extend(_analyze_async_opportunities(content))

    return opportunities


def _analyze_performance_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze performance improvement opportunities."""
    opportunities = []

    # Check for excessive cloning
    clone_count = content.count('.clone()')
    if clone_count > 5:
        opportunities.append({
            "type": "performance",
            "severity": "medium",
            "message": f"Excessive cloning detected ({clone_count} occurrences)",
            "suggestion": "Consider using references or Cow<str> to avoid unnecessary allocations"
        })

    # Check for String concatenation in loops
    if '+' in content and ('for ' in content or 'while ' in content):
        opportunities.append({
            "type": "performance",
            "severity": "medium",
            "message": "Potential string concatenation in loops",
            "suggestion": "Use format! macro or push_str for better performance"
        })

    # Check for Vec allocation without capacity
    if 'Vec::new()' in content and 'push(' in content:
        opportunities.append({
            "type": "performance",
            "severity": "low",
            "message": "Vec allocated without initial capacity",
            "suggestion": "Use Vec::with_capacity(n) when size is approximately known"
        })

    return opportunities


def _analyze_ownership_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze ownership and borrowing improvement opportunities."""
    opportunities = []

    # Check for unnecessary mutable references
    mutable_borrows = len(re.findall(r'&mut\s+', content))
    immutable_borrows = len(re.findall(r'&(?!mut)\s*\w+', content))

    if mutable_borrows > immutable_borrows * 0.5:
        opportunities.append({
            "type": "ownership",
            "severity": "medium",
            "message": "High ratio of mutable borrows",
            "suggestion": "Review if all mutable borrows are necessary"
        })

    # Check for potential move issues
    if 'moved value' in content or 'borrow checker' in content:
        opportunities.append({
            "type": "ownership",
            "severity": "high",
            "message": "Potential ownership or borrowing issues in comments",
            "suggestion": "Review ownership patterns and consider using references or smart pointers"
        })

    return opportunities


def _analyze_readability_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze readability improvement opportunities."""
    opportunities = []

    lines = content.split('\n')

    # Check for long functions
    functions = _extract_rust_functions(content)
    for func in functions:
        # Estimate function length (simplified)
        if func["name"] != "main":  # Skip main function
            opportunities.append({
                "type": "readability",
                "severity": "low",
                "message": f"Consider breaking down function '{func['name']}' if it's too long",
                "suggestion": "Extract logic into smaller, focused functions"
            })

    # Check for nested match statements
    nested_match_count = len(re.findall(r'match.*\{[^}]*match', content, re.DOTALL))
    if nested_match_count > 2:
        opportunities.append({
            "type": "readability",
            "severity": "medium",
            "message": f"Deep nesting with match statements ({nested_match_count})",
            "suggestion": "Consider extracting match arms into separate functions"
        })

    return opportunities


def _analyze_async_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze async code improvement opportunities."""
    opportunities = []

    if 'async' not in content:
        return opportunities

    # Check for blocking calls in async functions
    blocking_calls = ['std::thread::sleep', 'std::fs::', 'std::io::']
    for call in blocking_calls:
        if call in content:
            opportunities.append({
                "type": "async",
                "severity": "high",
                "message": f"Blocking call '{call}' detected in async context",
                "suggestion": "Use async alternatives like tokio::time::sleep or tokio::fs"
            })

    # Check for missing .await
    if 'async fn' in content and '.await' not in content:
        opportunities.append({
            "type": "async",
            "severity": "medium",
            "message": "Async function without await usage",
            "suggestion": "Ensure async operations are properly awaited"
        })

    return opportunities


def _format_rust_analysis_results(analysis: Dict[str, Any], analysis_type: str) -> str:
    """Format Rust analysis results for display."""
    output = []

    if analysis_type == "full":
        output.append("🦀 **Rust Code Analysis Report**\n")

        # Syntax info
        syntax = analysis.get("syntax", {})
        output.append(f"📄 **File Information:**")
        output.append(f"- Lines: {syntax.get('line_count', 0)}")
        output.append(f"- Functions: {len(syntax.get('functions', []))}")
        output.append(f"- Structs: {len(syntax.get('structs', []))}")
        output.append(f"- Enums: {len(syntax.get('enums', []))}")
        output.append(f"- Traits: {len(syntax.get('traits', []))}")
        output.append("")

        # Structure
        structure = analysis.get("structure", {})
        output.append(f"🏗️ **Code Structure:**")
        output.append(f"- Code lines: {structure.get('code_lines', 0)}")
        output.append(f"- Doc comments: {structure.get('doc_comments', 0)}")
        output.append(f"- Public items: {structure.get('public_items', 0)}")
        output.append(f"- Unsafe blocks: {structure.get('unsafe_blocks', 0)}")
        output.append(f"- Tests: {structure.get('test_functions', 0)}")
        output.append("")

        # Patterns
        patterns = analysis.get("patterns", {})
        error_handling = patterns.get("error_handling", {})
        ownership = patterns.get("ownership_patterns", {})

        output.append(f"🛡️ **Error Handling:**")
        output.append(f"- Result usage: {error_handling.get('result_usage', 0)}")
        output.append(f"- Unwrap calls: {error_handling.get('unwrap_calls', 0)}")
        output.append(f"- Question operator: {error_handling.get('question_operator', 0)}")
        output.append("")

        output.append(f"🔧 **Ownership Patterns:**")
        output.append(f"- Mutable borrows: {ownership.get('mutable_borrows', 0)}")
        output.append(f"- Immutable borrows: {ownership.get('immutable_borrows', 0)}")
        output.append(f"- Clone calls: {ownership.get('clone_calls', 0)}")
        output.append("")

        # Complexity
        complexity = analysis.get("complexity", {})
        output.append(f"📊 **Complexity:**")
        output.append(f"- Cyclomatic complexity: {complexity.get('cyclomatic_complexity', 0)}")
        output.append(f"- Max function complexity: {complexity.get('max_function_complexity', 0)}")
        output.append("")

        # Overall score
        score = analysis.get("overall_score", 0)
        output.append(f"⭐ **Overall Score: {score}/100**")

    else:
        output.append(f"🦀 **Rust {analysis_type.title()} Analysis:**")
        output.append(str(analysis)[:500] + "..." if len(str(analysis)) > 500 else str(analysis))

    return '\n'.join(output)


def _format_clippy_results(result: Dict[str, Any], suggestions: List[Dict], fix_suggestions: bool) -> str:
    """Format Clippy results for display."""
    output = []

    output.append("📎 **Clippy Analysis Report**\n")

    warnings = result.get("warnings", [])
    errors = result.get("errors", [])

    output.append(f"📊 **Summary:**")
    output.append(f"- Warnings: {len(warnings)}")
    output.append(f"- Errors: {len(errors)}")
    output.append("")

    if errors:
        output.append("🚨 **Errors:**")
        for error in errors[:5]:
            output.append(f"❌ {error}")
        if len(errors) > 5:
            output.append(f"... and {len(errors) - 5} more errors")
        output.append("")

    if warnings:
        output.append("⚠️ **Warnings:**")
        for warning in warnings[:10]:
            output.append(f"⚠️ {warning}")
        if len(warnings) > 10:
            output.append(f"... and {len(warnings) - 10} more warnings")
        output.append("")

    if fix_suggestions and suggestions:
        output.append("💡 **Fix Suggestions:**")
        for suggestion in suggestions[:5]:
            confidence = suggestion.get("confidence", "medium")
            confidence_emoji = {"high": "🟢", "medium": "🟡", "low": "🔴"}.get(confidence, "⚪")
            output.append(f"{confidence_emoji} {suggestion.get('suggestion', 'No suggestion')}")
        output.append("")

    return '\n'.join(output)


def _format_rust_refactor_suggestions(suggestions: List[Dict[str, Any]], focus: str) -> str:
    """Format Rust refactoring suggestions for display."""
    output = []

    output.append(f"🔄 **Rust Refactoring Suggestions ({focus})**\n")

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
        output.append(f"📝 **{suggestion_type.title()} Improvements:**")

        for item in items[:5]:  # Limit to 5 per type
            severity_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(item.get("severity"), "⚪")
            message = item.get("message", "No message")
            suggestion = item.get("suggestion", "No suggestion")

            output.append(f"{severity_icon} {message}")
            output.append(f"   💡 {suggestion}")
            output.append("")

        if len(items) > 5:
            output.append(f"   ... and {len(items) - 5} more items")
            output.append("")

    return '\n'.join(output)