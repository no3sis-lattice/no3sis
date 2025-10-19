"""
Rust Ownership and Borrowing Analysis Tools

Advanced tools for analyzing Rust's unique ownership system, borrowing patterns,
lifetimes, and memory safety guarantees.
"""

import re
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple


async def analyze_ownership(file_path: str, check_moves: bool = True) -> Dict[str, Any]:
    """
    Analyze Rust ownership and borrowing patterns.

    Args:
        file_path: Path to Rust file
        check_moves: Whether to analyze move semantics

    Returns:
        Dict with ownership analysis results
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

        if path.suffix != '.rs':
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ Not a Rust file: {file_path}"
                }],
                "success": False,
                "error": "not_rust_file"
            }

        content = path.read_text(encoding='utf-8')

        analysis = await _comprehensive_ownership_analysis(content, str(path), check_moves)

        formatted_output = _format_ownership_analysis_results(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": analysis,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Ownership analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def check_lifetimes(file_path: str) -> Dict[str, Any]:
    """
    Analyze lifetime annotations and borrowing relationships.

    Args:
        file_path: Path to Rust file

    Returns:
        Dict with lifetime analysis results
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

        analysis = await _analyze_lifetimes(content, str(path))

        formatted_output = _format_lifetime_analysis_results(analysis)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "analysis": analysis,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Lifetime analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_borrow_improvements(code_snippet: str, context: str = "") -> Dict[str, Any]:
    """
    Suggest improvements to borrowing patterns.

    Args:
        code_snippet: Code snippet to analyze
        context: Additional context about the code

    Returns:
        Dict with borrowing improvement suggestions
    """
    try:
        improvements = await _analyze_borrow_improvements(code_snippet, context)

        formatted_output = _format_borrow_improvements(improvements, code_snippet)

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
                "text": f"❌ Borrow improvement analysis failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

async def _comprehensive_ownership_analysis(content: str, file_path: str, check_moves: bool) -> Dict[str, Any]:
    """Perform comprehensive ownership analysis."""

    # Basic ownership patterns
    ownership_patterns = _analyze_ownership_patterns(content)

    # Borrowing analysis
    borrowing_analysis = _analyze_borrowing_patterns(content)

    # Smart pointer usage
    smart_pointers = _analyze_smart_pointer_usage(content)

    # Move semantics (if requested)
    move_analysis = _analyze_move_semantics(content) if check_moves else {}

    # Memory safety indicators
    safety_analysis = _analyze_memory_safety(content)

    # Potential issues
    ownership_issues = _detect_ownership_issues(content)

    return {
        "ownership_patterns": ownership_patterns,
        "borrowing": borrowing_analysis,
        "smart_pointers": smart_pointers,
        "move_semantics": move_analysis,
        "safety": safety_analysis,
        "issues": ownership_issues,
        "recommendations": _generate_ownership_recommendations(
            ownership_patterns, borrowing_analysis, smart_pointers, ownership_issues
        ),
        "ownership_score": _calculate_ownership_score(ownership_patterns, borrowing_analysis, ownership_issues)
    }


def _analyze_ownership_patterns(content: str) -> Dict[str, Any]:
    """Analyze ownership patterns in the code."""

    # Extract ownership-related patterns
    patterns = {
        "owned_values": _count_owned_values(content),
        "borrowed_values": _count_borrowed_values(content),
        "mutable_borrows": len(re.findall(r'&mut\s+\w+', content)),
        "immutable_borrows": len(re.findall(r'&(?!mut)\s+\w+', content)),
        "move_operations": len(re.findall(r'\bmove\b', content)),
        "copy_operations": _count_copy_operations(content),
        "clone_operations": len(re.findall(r'\.clone\(\)', content))
    }

    # Calculate ratios
    total_operations = sum(patterns.values())
    if total_operations > 0:
        patterns["move_ratio"] = patterns["move_operations"] / total_operations
        patterns["clone_ratio"] = patterns["clone_operations"] / total_operations
        patterns["borrow_ratio"] = (patterns["mutable_borrows"] + patterns["immutable_borrows"]) / total_operations
    else:
        patterns["move_ratio"] = 0.0
        patterns["clone_ratio"] = 0.0
        patterns["borrow_ratio"] = 0.0

    return patterns


def _analyze_borrowing_patterns(content: str) -> Dict[str, Any]:
    """Analyze borrowing patterns and relationships."""

    borrowing = {
        "borrow_count": len(re.findall(r'&\w+', content)),
        "mutable_borrow_count": len(re.findall(r'&mut\s+\w+', content)),
        "immutable_borrow_count": 0,  # Will be calculated
        "ref_patterns": len(re.findall(r'\bref\s+\w+', content)),
        "deref_operations": len(re.findall(r'\*\w+', content)),
        "borrow_checker_hints": _find_borrow_checker_hints(content)
    }

    borrowing["immutable_borrow_count"] = borrowing["borrow_count"] - borrowing["mutable_borrow_count"]

    # Analyze borrow safety
    borrowing["potential_conflicts"] = _detect_borrow_conflicts(content)
    borrowing["scope_analysis"] = _analyze_borrow_scopes(content)

    return borrowing


def _analyze_smart_pointer_usage(content: str) -> Dict[str, Any]:
    """Analyze smart pointer patterns."""

    smart_pointers = {
        "box_usage": {
            "count": len(re.findall(r'Box<[^>]+>', content)),
            "patterns": re.findall(r'Box<([^>]+)>', content)
        },
        "rc_usage": {
            "count": len(re.findall(r'Rc<[^>]+>', content)),
            "patterns": re.findall(r'Rc<([^>]+)>', content)
        },
        "arc_usage": {
            "count": len(re.findall(r'Arc<[^>]+>', content)),
            "patterns": re.findall(r'Arc<([^>]+)>', content)
        },
        "refcell_usage": {
            "count": len(re.findall(r'RefCell<[^>]+>', content)),
            "patterns": re.findall(r'RefCell<([^>]+)>', content)
        },
        "mutex_usage": {
            "count": len(re.findall(r'Mutex<[^>]+>', content)),
            "patterns": re.findall(r'Mutex<([^>]+)>', content)
        },
        "weak_usage": {
            "count": len(re.findall(r'Weak<[^>]+>', content)),
            "patterns": re.findall(r'Weak<([^>]+)>', content)
        }
    }

    # Analyze smart pointer patterns
    smart_pointers["interior_mutability"] = smart_pointers["refcell_usage"]["count"] > 0
    smart_pointers["shared_ownership"] = smart_pointers["rc_usage"]["count"] + smart_pointers["arc_usage"]["count"] > 0
    smart_pointers["thread_safety"] = smart_pointers["arc_usage"]["count"] + smart_pointers["mutex_usage"]["count"] > 0

    return smart_pointers


def _analyze_move_semantics(content: str) -> Dict[str, Any]:
    """Analyze move semantics and value transfers."""

    moves = {
        "explicit_moves": len(re.findall(r'\bmove\s+', content)),
        "implicit_moves": _detect_implicit_moves(content),
        "move_closures": len(re.findall(r'move\s*\|', content)),
        "consumption_patterns": _analyze_consumption_patterns(content)
    }

    return moves


def _analyze_memory_safety(content: str) -> Dict[str, Any]:
    """Analyze memory safety indicators."""

    safety = {
        "unsafe_blocks": len(re.findall(r'unsafe\s*\{', content)),
        "unsafe_functions": len(re.findall(r'unsafe\s+fn', content)),
        "raw_pointers": len(re.findall(r'\*(?:const|mut)\s+', content)),
        "transmute_usage": len(re.findall(r'transmute', content)),
        "uninitialized_usage": len(re.findall(r'uninitialized|MaybeUninit', content)),
        "drop_implications": _analyze_drop_patterns(content)
    }

    safety["safety_score"] = _calculate_safety_score(safety)

    return safety


def _detect_ownership_issues(content: str) -> List[Dict[str, Any]]:
    """Detect potential ownership and borrowing issues."""
    issues = []

    lines = content.split('\n')

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Detect potential issues
        if '.clone()' in stripped and 'Arc' not in stripped and 'Rc' not in stripped:
            issues.append({
                "type": "unnecessary_clone",
                "line": i,
                "severity": "medium",
                "message": "Potential unnecessary clone - consider using references",
                "suggestion": "Try using &T instead of T.clone() if possible"
            })

        if 'unwrap()' in stripped and ('Mutex' in stripped or 'RwLock' in stripped):
            issues.append({
                "type": "lock_unwrap",
                "line": i,
                "severity": "high",
                "message": "Unwrapping lock result - potential panic on poison",
                "suggestion": "Handle lock poisoning with proper error handling"
            })

        # Detect potential borrow checker issues
        if re.search(r'&mut.*&mut', stripped):
            issues.append({
                "type": "multiple_mutable_borrows",
                "line": i,
                "severity": "high",
                "message": "Potential multiple mutable borrows",
                "suggestion": "Ensure mutable borrows don't overlap in scope"
            })

        # Detect potential use-after-move
        if 'move' in stripped and any(var in stripped for var in ['use', 'print', 'return']):
            issues.append({
                "type": "potential_use_after_move",
                "line": i,
                "severity": "medium",
                "message": "Potential use of moved value",
                "suggestion": "Check that moved values aren't used after move"
            })

    return issues


async def _analyze_lifetimes(content: str, file_path: str) -> Dict[str, Any]:
    """Analyze lifetime annotations and relationships."""

    lifetime_analysis = {
        "lifetime_annotations": _extract_lifetime_annotations(content),
        "lifetime_parameters": _analyze_lifetime_parameters(content),
        "lifetime_bounds": _analyze_lifetime_bounds(content),
        "lifetime_elision": _analyze_lifetime_elision(content),
        "static_lifetimes": len(re.findall(r"'static", content)),
        "anonymous_lifetimes": len(re.findall(r"'_", content))
    }

    # Analyze lifetime relationships
    lifetime_analysis["relationships"] = _analyze_lifetime_relationships(content)
    lifetime_analysis["complexity_score"] = _calculate_lifetime_complexity(lifetime_analysis)

    return lifetime_analysis


def _extract_lifetime_annotations(content: str) -> List[Dict[str, Any]]:
    """Extract all lifetime annotations from the code."""
    lifetime_pattern = r"'([a-z]+)(?:\s*:\s*'[a-z]+)?"
    lifetimes = []

    for match in re.finditer(lifetime_pattern, content):
        lifetime_name = match.group(1)
        if lifetime_name not in ['static']:  # Exclude 'static as it's special
            lifetimes.append({
                "name": lifetime_name,
                "line": content[:match.start()].count('\n') + 1,
                "context": _get_lifetime_context(content, match.start(), match.end())
            })

    return lifetimes


def _analyze_lifetime_parameters(content: str) -> Dict[str, Any]:
    """Analyze lifetime parameters in function signatures and structs."""

    # Function lifetime parameters
    func_lifetimes = re.findall(r'fn\s+\w+<([^>]*\'[^>]*)>', content)

    # Struct lifetime parameters
    struct_lifetimes = re.findall(r'struct\s+\w+<([^>]*\'[^>]*)>', content)

    # Impl block lifetime parameters
    impl_lifetimes = re.findall(r'impl<([^>]*\'[^>]*)>', content)

    return {
        "function_lifetimes": len(func_lifetimes),
        "struct_lifetimes": len(struct_lifetimes),
        "impl_lifetimes": len(impl_lifetimes),
        "total_parameterized": len(func_lifetimes) + len(struct_lifetimes) + len(impl_lifetimes)
    }


def _analyze_lifetime_bounds(content: str) -> List[str]:
    """Analyze lifetime bounds and constraints."""
    # Pattern for lifetime bounds like 'a: 'b
    bound_pattern = r"'([a-z]+)\s*:\s*'([a-z]+)"
    bounds = re.findall(bound_pattern, content)

    return [f"'{a}: '{b}" for a, b in bounds]


def _analyze_lifetime_elision(content: str) -> Dict[str, Any]:
    """Analyze lifetime elision patterns."""

    # Functions without explicit lifetimes that might benefit from elision
    functions_with_refs = re.findall(r'fn\s+\w+\([^)]*&[^)]*\)\s*(?:->.*?&)?', content)

    elision_analysis = {
        "elision_candidates": len(functions_with_refs),
        "explicit_lifetime_functions": len(re.findall(r'fn\s+\w+<[^>]*\'[^>]*>', content)),
        "elision_ratio": 0.0
    }

    total_ref_functions = len(functions_with_refs) + elision_analysis["explicit_lifetime_functions"]
    if total_ref_functions > 0:
        elision_analysis["elision_ratio"] = len(functions_with_refs) / total_ref_functions

    return elision_analysis


def _analyze_lifetime_relationships(content: str) -> List[Dict[str, Any]]:
    """Analyze relationships between lifetimes."""
    relationships = []

    # Find lifetime bounds
    bounds = _analyze_lifetime_bounds(content)
    for bound in bounds:
        relationships.append({
            "type": "bound",
            "relationship": bound,
            "description": f"Lifetime constraint: {bound}"
        })

    # Find lifetime parameters that appear together
    param_pattern = r'<([^>]*\'[^>]*)>'
    for match in re.findall(param_pattern, content):
        lifetimes_in_params = re.findall(r"'([a-z]+)", match)
        if len(lifetimes_in_params) > 1:
            relationships.append({
                "type": "coexistence",
                "lifetimes": lifetimes_in_params,
                "description": f"Lifetimes that coexist: {', '.join(lifetimes_in_params)}"
            })

    return relationships


async def _analyze_borrow_improvements(code_snippet: str, context: str) -> List[Dict[str, Any]]:
    """Analyze code snippet for borrowing improvements."""
    improvements = []

    lines = code_snippet.split('\n')

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Suggest using references instead of cloning
        if '.clone()' in stripped and ('String' in stripped or 'Vec' in stripped):
            improvements.append({
                "type": "avoid_clone",
                "line": i,
                "priority": "medium",
                "message": "Consider using references instead of cloning",
                "before": stripped,
                "suggestion": "Try using &str instead of String.clone() or &[T] instead of Vec<T>.clone()",
                "example": "fn process(data: &str) instead of fn process(data: String)"
            })

        # Suggest borrowing for function parameters
        if re.search(r'fn\s+\w+\([^)]*String[^)]*\)', stripped):
            improvements.append({
                "type": "parameter_borrowing",
                "line": i,
                "priority": "high",
                "message": "Consider using &str instead of String for parameters",
                "before": stripped,
                "suggestion": "Use &str for read-only string parameters",
                "example": "fn process(s: &str) instead of fn process(s: String)"
            })

        # Suggest using Cow for conditional ownership
        if 'clone()' in stripped and ('if' in stripped or 'match' in stripped):
            improvements.append({
                "type": "cow_pattern",
                "line": i,
                "priority": "low",
                "message": "Consider using Cow<str> for conditional ownership",
                "before": stripped,
                "suggestion": "Use Cow<str> when you sometimes need to own and sometimes borrow",
                "example": "use std::borrow::Cow; fn process(s: Cow<str>)"
            })

        # Suggest smart pointer alternatives
        if '.clone()' in stripped and ('Arc' in context or 'thread' in context.lower()):
            improvements.append({
                "type": "smart_pointer",
                "line": i,
                "priority": "medium",
                "message": "Consider using Arc for shared ownership across threads",
                "before": stripped,
                "suggestion": "Use Arc<T> instead of cloning for thread-safe shared ownership",
                "example": "let shared = Arc::new(data); let clone = Arc::clone(&shared);"
            })

    return improvements


# Utility functions

def _count_owned_values(content: str) -> int:
    """Count patterns that indicate owned values."""
    patterns = [
        r'\bString::',
        r'\bVec::',
        r'\.to_string\(\)',
        r'\.to_owned\(\)',
        r'\bBox::new'
    ]

    count = 0
    for pattern in patterns:
        count += len(re.findall(pattern, content))

    return count


def _count_borrowed_values(content: str) -> int:
    """Count borrowed value patterns."""
    return len(re.findall(r'&\w+', content))


def _count_copy_operations(content: str) -> int:
    """Count copy trait usage."""
    # This is simplified - actual Copy trait usage is more complex
    copy_types = ['i32', 'i64', 'u32', 'u64', 'f32', 'f64', 'bool', 'char']
    count = 0

    for copy_type in copy_types:
        count += content.count(copy_type)

    return count


def _find_borrow_checker_hints(content: str) -> List[str]:
    """Find comments or patterns that indicate borrow checker issues."""
    hints = []

    # Look for common borrow checker related comments
    borrow_keywords = ['borrow', 'lifetime', 'move', 'ownership']

    for line in content.split('\n'):
        if '//' in line:
            comment = line[line.find('//'):]
            if any(keyword in comment.lower() for keyword in borrow_keywords):
                hints.append(comment.strip())

    return hints


def _detect_borrow_conflicts(content: str) -> List[Dict[str, Any]]:
    """Detect potential borrowing conflicts."""
    conflicts = []

    lines = content.split('\n')
    for i, line in enumerate(lines, 1):
        # This is a simplified check
        if '&mut' in line and '&' in line:
            mutable_count = line.count('&mut')
            immutable_count = line.count('&') - mutable_count

            if mutable_count > 0 and immutable_count > 0:
                conflicts.append({
                    "line": i,
                    "type": "mixed_borrows",
                    "description": "Line contains both mutable and immutable borrows"
                })

    return conflicts


def _analyze_borrow_scopes(content: str) -> Dict[str, Any]:
    """Analyze borrowing scopes."""
    # This is a simplified analysis
    return {
        "nested_scopes": content.count('{'),
        "potential_scope_issues": len(re.findall(r'&\w+.*\{.*\}.*&\w+', content))
    }


def _detect_implicit_moves(content: str) -> int:
    """Detect patterns that cause implicit moves."""
    # Simplified detection of patterns that cause moves
    move_patterns = [
        r'\w+\s*\(',  # Function calls that might consume
        r'return\s+\w+',  # Return statements
        r'let\s+\w+\s*=\s*\w+\s*;'  # Variable assignments
    ]

    count = 0
    for pattern in move_patterns:
        count += len(re.findall(pattern, content))

    return count


def _analyze_consumption_patterns(content: str) -> List[str]:
    """Analyze value consumption patterns."""
    patterns = []

    # Look for consuming method calls
    consuming_methods = ['into_iter', 'into_bytes', 'into_string']
    for method in consuming_methods:
        if f'.{method}(' in content:
            patterns.append(method)

    return patterns


def _analyze_drop_patterns(content: str) -> Dict[str, Any]:
    """Analyze Drop trait usage and RAII patterns."""
    return {
        "explicit_drops": len(re.findall(r'drop\s*\(', content)),
        "drop_implementations": len(re.findall(r'impl.*Drop.*for', content)),
        "raii_patterns": len(re.findall(r'struct.*\{.*File.*\}', content))  # Simplified RAII detection
    }


def _calculate_safety_score(safety: Dict[str, Any]) -> int:
    """Calculate memory safety score."""
    score = 100

    # Deduct points for unsafe usage
    score -= safety["unsafe_blocks"] * 20
    score -= safety["unsafe_functions"] * 25
    score -= safety["raw_pointers"] * 15
    score -= safety["transmute_usage"] * 30

    return max(0, score)


def _calculate_ownership_score(ownership: Dict, borrowing: Dict, issues: List) -> int:
    """Calculate overall ownership pattern score."""
    score = 100

    # Deduct for issues
    for issue in issues:
        if issue["severity"] == "high":
            score -= 20
        elif issue["severity"] == "medium":
            score -= 10
        else:
            score -= 5

    # Reward good patterns
    if ownership.get("borrow_ratio", 0) > 0.6:  # High borrowing ratio is good
        score += 10

    if ownership.get("clone_ratio", 0) < 0.2:  # Low cloning ratio is good
        score += 10

    # Deduct for potential borrow conflicts
    score -= len(borrowing.get("potential_conflicts", [])) * 15

    return max(0, min(100, score))


def _calculate_lifetime_complexity(lifetime_analysis: Dict) -> int:
    """Calculate lifetime complexity score."""
    complexity = 0

    complexity += len(lifetime_analysis.get("lifetime_annotations", [])) * 2
    complexity += lifetime_analysis.get("lifetime_parameters", {}).get("total_parameterized", 0) * 3
    complexity += len(lifetime_analysis.get("lifetime_bounds", [])) * 4
    complexity += len(lifetime_analysis.get("relationships", [])) * 2

    return complexity


def _get_lifetime_context(content: str, start: int, end: int) -> str:
    """Get context around a lifetime annotation."""
    # Get surrounding context (50 characters before and after)
    context_start = max(0, start - 50)
    context_end = min(len(content), end + 50)

    return content[context_start:context_end].strip()


def _generate_ownership_recommendations(ownership: Dict, borrowing: Dict, smart_pointers: Dict, issues: List) -> List[Dict[str, Any]]:
    """Generate ownership pattern recommendations."""
    recommendations = []

    # High clone ratio recommendation
    if ownership.get("clone_ratio", 0) > 0.3:
        recommendations.append({
            "type": "reduce_cloning",
            "priority": "high",
            "message": "High cloning ratio detected - consider using references",
            "benefit": "Reduced memory allocations and improved performance",
            "suggestion": "Use &T instead of T.clone() where possible"
        })

    # Smart pointer recommendations
    if borrowing.get("borrow_count", 0) > 10 and smart_pointers.get("rc_usage", {}).get("count", 0) == 0:
        recommendations.append({
            "type": "shared_ownership",
            "priority": "medium",
            "message": "Consider Rc<T> for shared ownership scenarios",
            "benefit": "Cleaner ownership semantics for shared data",
            "suggestion": "Use Rc<T> when multiple owners need read access"
        })

    # Thread safety recommendations
    if smart_pointers.get("rc_usage", {}).get("count", 0) > 0 and "thread" in str(issues):
        recommendations.append({
            "type": "thread_safety",
            "priority": "high",
            "message": "Use Arc<T> instead of Rc<T> for thread-safe shared ownership",
            "benefit": "Thread safety and prevention of data races",
            "suggestion": "Replace Rc<T> with Arc<T> for multi-threaded code"
        })

    # Issues-based recommendations
    high_severity_issues = [issue for issue in issues if issue["severity"] == "high"]
    if high_severity_issues:
        recommendations.append({
            "type": "critical_fixes",
            "priority": "critical",
            "message": f"{len(high_severity_issues)} critical ownership issues found",
            "benefit": "Prevention of runtime panics and memory safety",
            "suggestion": "Address critical ownership violations immediately"
        })

    return recommendations


# Formatting functions

def _format_ownership_analysis_results(analysis: Dict[str, Any]) -> str:
    """Format ownership analysis results for display."""
    output = []

    output.append("🦀 **Rust Ownership Analysis**\n")

    # Ownership patterns
    ownership = analysis.get("ownership_patterns", {})
    output.append("🔧 **Ownership Patterns:**")
    output.append(f"- Owned values: {ownership.get('owned_values', 0)}")
    output.append(f"- Borrowed values: {ownership.get('borrowed_values', 0)}")
    output.append(f"- Clone operations: {ownership.get('clone_operations', 0)}")
    output.append(f"- Move operations: {ownership.get('move_operations', 0)}")

    # Ratios
    clone_ratio = ownership.get('clone_ratio', 0)
    borrow_ratio = ownership.get('borrow_ratio', 0)
    output.append(f"- Clone ratio: {clone_ratio:.2%}")
    output.append(f"- Borrow ratio: {borrow_ratio:.2%}")
    output.append("")

    # Borrowing analysis
    borrowing = analysis.get("borrowing", {})
    output.append("📎 **Borrowing Analysis:**")
    output.append(f"- Mutable borrows: {borrowing.get('mutable_borrow_count', 0)}")
    output.append(f"- Immutable borrows: {borrowing.get('immutable_borrow_count', 0)}")
    output.append(f"- Deref operations: {borrowing.get('deref_operations', 0)}")

    conflicts = borrowing.get("potential_conflicts", [])
    if conflicts:
        output.append(f"⚠️ Potential borrow conflicts: {len(conflicts)}")
    output.append("")

    # Smart pointers
    smart_pointers = analysis.get("smart_pointers", {})
    smart_pointer_usage = []
    for sp_type, data in smart_pointers.items():
        if isinstance(data, dict) and data.get("count", 0) > 0:
            smart_pointer_usage.append(f"{sp_type}: {data['count']}")

    if smart_pointer_usage:
        output.append("📦 **Smart Pointers:**")
        for usage in smart_pointer_usage:
            output.append(f"- {usage}")
        output.append("")

    # Safety analysis
    safety = analysis.get("safety", {})
    safety_score = safety.get("safety_score", 100)
    score_emoji = "🟢" if safety_score >= 90 else "🟡" if safety_score >= 70 else "🔴"
    output.append(f"{score_emoji} **Memory Safety Score: {safety_score}/100**")

    if safety.get("unsafe_blocks", 0) > 0:
        output.append(f"⚠️ Unsafe blocks: {safety['unsafe_blocks']}")
    output.append("")

    # Issues
    issues = analysis.get("issues", [])
    if issues:
        output.append("🚨 **Ownership Issues:**")
        for issue in issues[:5]:  # Show first 5 issues
            severity_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(issue["severity"], "⚪")
            output.append(f"{severity_icon} Line {issue['line']}: {issue['message']}")
            output.append(f"   💡 {issue['suggestion']}")

        if len(issues) > 5:
            output.append(f"... and {len(issues) - 5} more issues")
        output.append("")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"critical": "🚨", "high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")
            if rec.get("benefit"):
                output.append(f"   ✅ {rec['benefit']}")
        output.append("")

    # Overall score
    ownership_score = analysis.get("ownership_score", 0)
    output.append(f"⭐ **Overall Ownership Score: {ownership_score}/100**")

    return '\n'.join(output)


def _format_lifetime_analysis_results(analysis: Dict[str, Any]) -> str:
    """Format lifetime analysis results for display."""
    output = []

    output.append("⏳ **Rust Lifetime Analysis**\n")

    # Basic lifetime info
    annotations = analysis.get("lifetime_annotations", [])
    output.append(f"📝 **Lifetime Annotations: {len(annotations)}**")

    if annotations:
        for annotation in annotations[:5]:  # Show first 5
            output.append(f"- '{annotation['name']}' at line {annotation['line']}")
        if len(annotations) > 5:
            output.append(f"... and {len(annotations) - 5} more")
        output.append("")

    # Lifetime parameters
    params = analysis.get("lifetime_parameters", {})
    output.append("🔧 **Lifetime Parameters:**")
    output.append(f"- Function lifetimes: {params.get('function_lifetimes', 0)}")
    output.append(f"- Struct lifetimes: {params.get('struct_lifetimes', 0)}")
    output.append(f"- Impl lifetimes: {params.get('impl_lifetimes', 0)}")
    output.append("")

    # Lifetime bounds
    bounds = analysis.get("lifetime_bounds", [])
    if bounds:
        output.append("🔗 **Lifetime Bounds:**")
        for bound in bounds:
            output.append(f"- {bound}")
        output.append("")

    # Elision analysis
    elision = analysis.get("lifetime_elision", {})
    elision_ratio = elision.get("elision_ratio", 0)
    output.append(f"⚡ **Lifetime Elision: {elision_ratio:.1%} of functions use elision**")
    output.append("")

    # Complexity
    complexity = analysis.get("complexity_score", 0)
    complexity_emoji = "🟢" if complexity < 10 else "🟡" if complexity < 20 else "🔴"
    output.append(f"{complexity_emoji} **Lifetime Complexity Score: {complexity}**")

    # Relationships
    relationships = analysis.get("relationships", [])
    if relationships:
        output.append("\n🌐 **Lifetime Relationships:**")
        for rel in relationships[:3]:  # Show first 3
            output.append(f"- {rel.get('description', 'Unknown relationship')}")

    return '\n'.join(output)


def _format_borrow_improvements(improvements: List[Dict[str, Any]], code_snippet: str) -> str:
    """Format borrow improvement suggestions for display."""
    output = []

    output.append("💡 **Borrowing Improvement Suggestions**\n")

    if not improvements:
        output.append("✅ No borrowing improvements suggested!")
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
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(item.get("priority"), "⚪")
            line = item.get("line", "?")
            message = item.get("message", "No message")
            suggestion = item.get("suggestion", "No suggestion")
            example = item.get("example", "")

            output.append(f"{priority_emoji} Line {line}: {message}")
            output.append(f"   💡 {suggestion}")
            if example:
                output.append(f"   📄 Example: `{example}`")
            output.append("")

    return '\n'.join(output)