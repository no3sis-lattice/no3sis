"""
Rust Async Programming and Performance Analysis Tools

Advanced tools for analyzing async patterns, error handling, and performance
optimization opportunities in Rust code.
"""

import re
from pathlib import Path
from typing import Dict, Any, List, Optional


async def analyze_async_patterns(file_path: str) -> Dict[str, Any]:
    """
    Analyze async/await patterns and Tokio usage.

    Args:
        file_path: Path to Rust file

    Returns:
        Dict with async pattern analysis results
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

        analysis = await _comprehensive_async_analysis(content, str(path))

        formatted_output = _format_async_analysis_results(analysis)

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
                "text": f"❌ Async analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def check_error_handling(file_path: str) -> Dict[str, Any]:
    """
    Analyze Rust error handling patterns and Result usage.

    Args:
        file_path: Path to Rust file

    Returns:
        Dict with error handling analysis results
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

        analysis = await _comprehensive_error_handling_analysis(content, str(path))

        formatted_output = _format_error_handling_results(analysis)

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
                "text": f"❌ Error handling analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def suggest_performance_improvements(file_path: str) -> Dict[str, Any]:
    """
    Suggest performance improvements for Rust code.

    Args:
        file_path: Path to Rust file

    Returns:
        Dict with performance improvement suggestions
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

        suggestions = await _analyze_performance_opportunities(content, str(path))

        formatted_output = _format_performance_suggestions(suggestions)

        return {
            "content": [{
                "type": "text",
                "text": formatted_output
            }],
            "success": True,
            "suggestions": suggestions,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Performance analysis failed for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


# Internal helper functions

async def _comprehensive_async_analysis(content: str, file_path: str) -> Dict[str, Any]:
    """Perform comprehensive async pattern analysis."""

    # Basic async detection
    async_detection = _detect_async_patterns(content)

    # Tokio-specific analysis
    tokio_analysis = _analyze_tokio_patterns(content)

    # Async runtime patterns
    runtime_patterns = _analyze_runtime_patterns(content)

    # Concurrency patterns
    concurrency_analysis = _analyze_concurrency_patterns(content)

    # Async error handling
    async_error_handling = _analyze_async_error_patterns(content)

    # Performance considerations
    async_performance = _analyze_async_performance_patterns(content)

    return {
        "detection": async_detection,
        "tokio": tokio_analysis,
        "runtime": runtime_patterns,
        "concurrency": concurrency_analysis,
        "error_handling": async_error_handling,
        "performance": async_performance,
        "recommendations": _generate_async_recommendations(
            async_detection, tokio_analysis, concurrency_analysis, async_performance
        ),
        "async_score": _calculate_async_quality_score(
            async_detection, async_error_handling, async_performance
        )
    }


def _detect_async_patterns(content: str) -> Dict[str, Any]:
    """Detect basic async patterns."""
    return {
        "async_functions": len(re.findall(r'async\s+fn\s+\w+', content)),
        "await_calls": len(re.findall(r'\.await', content)),
        "async_blocks": len(re.findall(r'async\s+(?:move\s+)?\{', content)),
        "async_closures": len(re.findall(r'async\s+(?:move\s+)?\|', content)),
        "future_usage": len(re.findall(r'Future<', content)),
        "pin_usage": len(re.findall(r'Pin<', content)),
        "stream_usage": len(re.findall(r'Stream<', content)),
        "has_async": 'async' in content
    }


def _analyze_tokio_patterns(content: str) -> Dict[str, Any]:
    """Analyze Tokio-specific patterns."""
    tokio_patterns = {
        "tokio_main": bool(re.search(r'#\[tokio::main\]', content)),
        "tokio_test": len(re.findall(r'#\[tokio::test\]', content)),
        "spawn_calls": len(re.findall(r'tokio::spawn\s*\(', content)),
        "select_usage": len(re.findall(r'tokio::select!\s*\{', content)),
        "join_usage": len(re.findall(r'tokio::join!\s*\(', content)),
        "try_join_usage": len(re.findall(r'tokio::try_join!\s*\(', content)),
        "timeout_usage": len(re.findall(r'tokio::time::timeout', content)),
        "sleep_usage": len(re.findall(r'tokio::time::sleep', content)),
        "mpsc_usage": len(re.findall(r'tokio::sync::mpsc', content)),
        "oneshot_usage": len(re.findall(r'tokio::sync::oneshot', content)),
        "mutex_usage": len(re.findall(r'tokio::sync::Mutex', content)),
        "rwlock_usage": len(re.findall(r'tokio::sync::RwLock', content)),
        "semaphore_usage": len(re.findall(r'tokio::sync::Semaphore', content))
    }

    tokio_patterns["uses_tokio"] = any(count > 0 for count in tokio_patterns.values())
    tokio_patterns["sync_primitive_count"] = (
        tokio_patterns["mpsc_usage"] + tokio_patterns["oneshot_usage"] +
        tokio_patterns["mutex_usage"] + tokio_patterns["rwlock_usage"] +
        tokio_patterns["semaphore_usage"]
    )

    return tokio_patterns


def _analyze_runtime_patterns(content: str) -> Dict[str, Any]:
    """Analyze async runtime patterns."""
    return {
        "runtime_creation": len(re.findall(r'Runtime::new\s*\(\)', content)),
        "runtime_block_on": len(re.findall(r'\.block_on\s*\(', content)),
        "executor_spawn": len(re.findall(r'executor::spawn', content)),
        "async_std_usage": len(re.findall(r'async_std::', content)),
        "smol_usage": len(re.findall(r'smol::', content)),
        "futures_usage": len(re.findall(r'futures::', content))
    }


def _analyze_concurrency_patterns(content: str) -> Dict[str, Any]:
    """Analyze concurrency and parallelism patterns."""
    concurrency = {
        "spawn_blocking": len(re.findall(r'spawn_blocking\s*\(', content)),
        "rayon_usage": len(re.findall(r'rayon::', content)),
        "par_iter": len(re.findall(r'\.par_iter\s*\(\)', content)),
        "crossbeam_usage": len(re.findall(r'crossbeam::', content)),
        "thread_spawn": len(re.findall(r'thread::spawn\s*\(', content)),
        "arc_usage": len(re.findall(r'Arc<[^>]+>', content)),
        "mutex_std": len(re.findall(r'std::sync::Mutex', content)),
        "rwlock_std": len(re.findall(r'std::sync::RwLock', content))
    }

    # Calculate concurrency complexity
    concurrency["total_concurrency_primitives"] = sum(concurrency.values())
    concurrency["uses_parallel_processing"] = (
        concurrency["rayon_usage"] > 0 or concurrency["par_iter"] > 0
    )

    return concurrency


def _analyze_async_error_patterns(content: str) -> Dict[str, Any]:
    """Analyze error handling in async context."""
    return {
        "async_result_functions": len(re.findall(r'async\s+fn\s+\w+[^{]*->\s*Result<', content)),
        "await_question_mark": len(re.findall(r'\.await\?', content)),
        "async_unwrap": len(re.findall(r'\.await\.unwrap\s*\(\)', content)),
        "async_expect": len(re.findall(r'\.await\.expect\s*\(', content)),
        "async_match_result": len(re.findall(r'match\s+[^{]*\.await\s*\{', content)),
        "try_join_pattern": len(re.findall(r'try_join!\s*\(', content))
    }


def _analyze_async_performance_patterns(content: str) -> Dict[str, Any]:
    """Analyze async performance patterns."""
    performance = {
        "buffered_streams": len(re.findall(r'\.buffered\s*\(', content)),
        "buffer_unordered": len(re.findall(r'\.buffer_unordered\s*\(', content)),
        "for_each_concurrent": len(re.findall(r'\.for_each_concurrent\s*\(', content)),
        "yield_now": len(re.findall(r'tokio::task::yield_now', content)),
        "spawn_local": len(re.findall(r'spawn_local\s*\(', content)),
        "blocking_calls": _detect_blocking_calls_in_async(content),
        "large_futures": _detect_large_future_chains(content)
    }

    # Performance issues
    performance["potential_issues"] = []
    if performance["blocking_calls"] > 0:
        performance["potential_issues"].append("Blocking calls in async context")
    if performance["large_futures"] > 3:
        performance["potential_issues"].append("Complex future chains detected")

    return performance


def _detect_blocking_calls_in_async(content: str) -> int:
    """Detect potentially blocking calls in async functions."""
    blocking_patterns = [
        r'std::fs::', r'std::io::', r'std::thread::sleep',
        r'\.read_to_string\s*\(', r'\.write_all\s*\(',
        r'std::process::'
    ]

    # Look for these patterns in async functions
    async_functions = re.findall(r'async\s+fn\s+\w+[^{]*\{[^}]*\}', content, re.DOTALL)
    blocking_count = 0

    for func in async_functions:
        for pattern in blocking_patterns:
            blocking_count += len(re.findall(pattern, func))

    return blocking_count


def _detect_large_future_chains(content: str) -> int:
    """Detect complex future chains that might impact performance."""
    # Look for chains of .then(), .and_then(), .map(), etc.
    chain_patterns = [
        r'\.(?:then|and_then|or_else|map|map_err)\s*\([^)]*\)\s*\.(?:then|and_then|or_else|map|map_err)',
        r'\.await[^.]*\.[^.]*\.await[^.]*\.[^.]*\.await'  # Multiple awaits in sequence
    ]

    chain_count = 0
    for pattern in chain_patterns:
        chain_count += len(re.findall(pattern, content))

    return chain_count


async def _comprehensive_error_handling_analysis(content: str, file_path: str) -> Dict[str, Any]:
    """Perform comprehensive error handling analysis."""

    # Basic error patterns
    error_patterns = _analyze_error_patterns(content)

    # Custom error types
    custom_errors = _analyze_custom_error_types(content)

    # Error propagation
    propagation = _analyze_error_propagation(content)

    # Error library usage
    error_libraries = _analyze_error_library_usage(content)

    # Error handling best practices
    best_practices = _analyze_error_best_practices(content)

    return {
        "patterns": error_patterns,
        "custom_errors": custom_errors,
        "propagation": propagation,
        "libraries": error_libraries,
        "best_practices": best_practices,
        "recommendations": _generate_error_handling_recommendations(
            error_patterns, custom_errors, propagation, best_practices
        ),
        "error_handling_score": _calculate_error_handling_score(
            error_patterns, propagation, best_practices
        )
    }


def _analyze_error_patterns(content: str) -> Dict[str, Any]:
    """Analyze basic error handling patterns."""
    return {
        "result_returns": len(re.findall(r'->\s*Result<[^>]+>', content)),
        "option_returns": len(re.findall(r'->\s*Option<[^>]+>', content)),
        "question_mark_usage": len(re.findall(r'\?\s*[;}]', content)),
        "unwrap_calls": len(re.findall(r'\.unwrap\s*\(\)', content)),
        "expect_calls": len(re.findall(r'\.expect\s*\(', content)),
        "panic_calls": len(re.findall(r'panic!\s*\(', content)),
        "match_result": len(re.findall(r'match\s+[^{]*\{[^}]*Ok\s*\([^)]*\)[^}]*Err\s*\([^)]*\)', content, re.DOTALL)),
        "if_let_ok": len(re.findall(r'if\s+let\s+Ok\s*\([^)]*\)', content)),
        "if_let_err": len(re.findall(r'if\s+let\s+Err\s*\([^)]*\)', content))
    }


def _analyze_custom_error_types(content: str) -> Dict[str, Any]:
    """Analyze custom error type definitions."""
    custom_errors = {
        "error_enums": len(re.findall(r'enum\s+\w*Error\s*\{', content)),
        "error_structs": len(re.findall(r'struct\s+\w*Error\s*\{', content)),
        "error_trait_impls": len(re.findall(r'impl.*Error.*for\s+\w+', content)),
        "display_impls": len(re.findall(r'impl.*Display.*for\s+\w+', content)),
        "from_impls": len(re.findall(r'impl.*From<[^>]+>.*for\s+\w+', content))
    }

    custom_errors["has_custom_errors"] = any(count > 0 for count in custom_errors.values())

    return custom_errors


def _analyze_error_propagation(content: str) -> Dict[str, Any]:
    """Analyze error propagation patterns."""
    return {
        "question_mark_chains": len(re.findall(r'\?[^?]*\?', content)),
        "map_err_usage": len(re.findall(r'\.map_err\s*\(', content)),
        "error_context": len(re.findall(r'\.context\s*\(', content)),
        "with_context": len(re.findall(r'\.with_context\s*\(', content)),
        "error_chaining": len(re.findall(r'\.chain_err\s*\(', content)),
        "early_returns": len(re.findall(r'return\s+Err\s*\(', content))
    }


def _analyze_error_library_usage(content: str) -> Dict[str, Any]:
    """Analyze usage of error handling libraries."""
    return {
        "anyhow": {
            "usage": "anyhow::" in content or "use anyhow" in content,
            "result_type": len(re.findall(r'anyhow::Result', content)),
            "context_usage": len(re.findall(r'\.context\s*\(', content)),
            "bail_usage": len(re.findall(r'bail!\s*\(', content))
        },
        "thiserror": {
            "usage": "thiserror::" in content or "use thiserror" in content,
            "error_derive": len(re.findall(r'#\[derive\([^)]*Error[^)]*\)\]', content)),
            "error_attr": len(re.findall(r'#\[error\s*\(', content))
        },
        "eyre": {
            "usage": "eyre::" in content or "use eyre" in content,
            "report_type": len(re.findall(r'eyre::Report', content))
        }
    }


def _analyze_error_best_practices(content: str) -> Dict[str, Any]:
    """Analyze adherence to error handling best practices."""
    best_practices = {
        "avoid_unwrap": _calculate_unwrap_to_expect_ratio(content),
        "error_documentation": _check_error_documentation(content),
        "consistent_error_types": _check_error_type_consistency(content),
        "proper_error_context": _check_error_context_usage(content)
    }

    return best_practices


def _calculate_unwrap_to_expect_ratio(content: str) -> Dict[str, Any]:
    """Calculate ratio of unwrap vs expect usage."""
    unwrap_count = len(re.findall(r'\.unwrap\s*\(\)', content))
    expect_count = len(re.findall(r'\.expect\s*\(', content))
    total = unwrap_count + expect_count

    return {
        "unwrap_count": unwrap_count,
        "expect_count": expect_count,
        "expect_ratio": expect_count / total if total > 0 else 0.0,
        "score": expect_count / total * 100 if total > 0 else 100
    }


def _check_error_documentation(content: str) -> Dict[str, Any]:
    """Check for error documentation."""
    functions_with_results = len(re.findall(r'fn\s+\w+[^{]*->\s*Result<', content))
    documented_functions = len(re.findall(r'///[^}]*fn\s+\w+[^{]*->\s*Result<', content, re.DOTALL))

    return {
        "functions_with_results": functions_with_results,
        "documented_functions": documented_functions,
        "documentation_ratio": documented_functions / functions_with_results if functions_with_results > 0 else 0.0
    }


def _check_error_type_consistency(content: str) -> Dict[str, Any]:
    """Check for consistent error type usage."""
    # Extract error types from Result returns
    error_types = re.findall(r'Result<[^,]+,\s*([^>]+)>', content)
    unique_error_types = set(error_types)

    return {
        "total_error_returns": len(error_types),
        "unique_error_types": len(unique_error_types),
        "consistency_score": 1.0 / len(unique_error_types) if unique_error_types else 1.0
    }


def _check_error_context_usage(content: str) -> Dict[str, Any]:
    """Check for proper error context usage."""
    context_usage = len(re.findall(r'\.(?:context|with_context)\s*\(', content))
    question_marks = len(re.findall(r'\?\s*[;}]', content))

    return {
        "context_usage": context_usage,
        "question_marks": question_marks,
        "context_ratio": context_usage / question_marks if question_marks > 0 else 0.0
    }


async def _analyze_performance_opportunities(content: str, file_path: str) -> List[Dict[str, Any]]:
    """Analyze performance improvement opportunities."""
    opportunities = []

    # Memory allocation opportunities
    opportunities.extend(_analyze_allocation_opportunities(content))

    # Iterator optimization opportunities
    opportunities.extend(_analyze_iterator_opportunities(content))

    # String handling opportunities
    opportunities.extend(_analyze_string_opportunities(content))

    # Collection optimization opportunities
    opportunities.extend(_analyze_collection_opportunities(content))

    # Async performance opportunities
    opportunities.extend(_analyze_async_performance_opportunities(content))

    return opportunities


def _analyze_allocation_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze memory allocation optimization opportunities."""
    opportunities = []

    # Excessive cloning
    clone_count = len(re.findall(r'\.clone\s*\(\)', content))
    if clone_count > 5:
        opportunities.append({
            "type": "memory_allocation",
            "priority": "medium",
            "message": f"Excessive cloning detected ({clone_count} occurrences)",
            "suggestion": "Consider using references or Cow<T> to reduce allocations",
            "impact": "Memory usage reduction"
        })

    # Vec without capacity
    vec_new_count = len(re.findall(r'Vec::new\s*\(\)', content))
    if vec_new_count > 3:
        opportunities.append({
            "type": "memory_allocation",
            "priority": "low",
            "message": f"Vec::new() used {vec_new_count} times",
            "suggestion": "Use Vec::with_capacity(n) when size is known",
            "impact": "Reduced reallocations"
        })

    # String concatenation in loops
    if '+' in content and any(loop in content for loop in ['for ', 'while ', 'loop ']):
        opportunities.append({
            "type": "memory_allocation",
            "priority": "medium",
            "message": "Potential string concatenation in loops",
            "suggestion": "Use String::with_capacity() and push_str() instead of +",
            "impact": "Reduced string reallocations"
        })

    return opportunities


def _analyze_iterator_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze iterator optimization opportunities."""
    opportunities = []

    # Iterator vs for loop
    for_loops = len(re.findall(r'for\s+\w+\s+in\s+', content))
    iterator_chains = len(re.findall(r'\.iter\s*\(\)[^.]*\.', content))

    if for_loops > iterator_chains * 2:
        opportunities.append({
            "type": "iterator_optimization",
            "priority": "low",
            "message": "Consider using iterator chains instead of for loops",
            "suggestion": "Use .iter().map().filter().collect() patterns",
            "impact": "More idiomatic and potentially faster code"
        })

    # Collect to Vec when not needed
    unnecessary_collect = len(re.findall(r'\.collect::<Vec<[^>]+>>\s*\(\)[^.]*\.iter\s*\(\)', content))
    if unnecessary_collect > 0:
        opportunities.append({
            "type": "iterator_optimization",
            "priority": "medium",
            "message": "Unnecessary collect() followed by iter()",
            "suggestion": "Remove intermediate collect() calls",
            "impact": "Avoid unnecessary allocations"
        })

    return opportunities


def _analyze_string_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze string handling optimization opportunities."""
    opportunities = []

    # String vs &str in function parameters
    string_params = len(re.findall(r'fn\s+\w+\s*\([^)]*String[^)]*\)', content))
    if string_params > 2:
        opportunities.append({
            "type": "string_optimization",
            "priority": "medium",
            "message": f"Functions taking String parameters: {string_params}",
            "suggestion": "Consider using &str for read-only string parameters",
            "impact": "Avoid unnecessary String allocations"
        })

    # format! for simple concatenations
    format_simple = len(re.findall(r'format!\s*\(\s*"[^"]*\{\}[^"]*"\s*,\s*\w+\s*\)', content))
    if format_simple > 3:
        opportunities.append({
            "type": "string_optimization",
            "priority": "low",
            "message": "Simple format! usage detected",
            "suggestion": "Consider using + or push_str for simple concatenations",
            "impact": "Reduced formatting overhead"
        })

    return opportunities


def _analyze_collection_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze collection optimization opportunities."""
    opportunities = []

    # HashMap usage without capacity
    hashmap_new = len(re.findall(r'HashMap::new\s*\(\)', content))
    if hashmap_new > 2:
        opportunities.append({
            "type": "collection_optimization",
            "priority": "low",
            "message": "HashMap::new() without capacity hint",
            "suggestion": "Use HashMap::with_capacity(n) when size is known",
            "impact": "Reduced hash map reallocations"
        })

    return opportunities


def _analyze_async_performance_opportunities(content: str) -> List[Dict[str, Any]]:
    """Analyze async-specific performance opportunities."""
    opportunities = []

    if 'async' not in content:
        return opportunities

    # Sequential awaits
    sequential_awaits = len(re.findall(r'\.await[^.]*\n[^.]*\.await', content))
    if sequential_awaits > 2:
        opportunities.append({
            "type": "async_performance",
            "priority": "medium",
            "message": "Sequential await calls detected",
            "suggestion": "Use join! or try_join! for concurrent execution",
            "impact": "Improved concurrency and reduced latency"
        })

    # Missing buffering in streams
    if '.for_each(' in content and '.buffered(' not in content:
        opportunities.append({
            "type": "async_performance",
            "priority": "low",
            "message": "Stream processing without buffering",
            "suggestion": "Consider using .buffered(n) for concurrent stream processing",
            "impact": "Better stream processing performance"
        })

    return opportunities


# Recommendation generation functions

def _generate_async_recommendations(detection: Dict, tokio: Dict,
                                   concurrency: Dict, performance: Dict) -> List[Dict[str, Any]]:
    """Generate async programming recommendations."""
    recommendations = []

    # Tokio usage recommendations
    if detection.get("has_async", False) and not tokio.get("uses_tokio", False):
        recommendations.append({
            "type": "async_runtime",
            "priority": "medium",
            "message": "Async code detected without Tokio runtime",
            "suggestion": "Consider using Tokio for comprehensive async runtime support"
        })

    # Error handling in async context
    if detection.get("async_functions", 0) > 0 and performance.get("blocking_calls", 0) > 0:
        recommendations.append({
            "type": "blocking_calls",
            "priority": "high",
            "message": "Blocking calls detected in async functions",
            "suggestion": "Use async alternatives or spawn_blocking for blocking operations"
        })

    # Concurrency recommendations
    total_primitives = concurrency.get("total_concurrency_primitives", 0)
    if total_primitives > 5:
        recommendations.append({
            "type": "complexity",
            "priority": "medium",
            "message": f"High concurrency complexity ({total_primitives} primitives)",
            "suggestion": "Consider simplifying concurrency patterns or using higher-level abstractions"
        })

    return recommendations


def _generate_error_handling_recommendations(patterns: Dict, custom_errors: Dict,
                                           propagation: Dict, best_practices: Dict) -> List[Dict[str, Any]]:
    """Generate error handling recommendations."""
    recommendations = []

    # Unwrap vs expect recommendations
    unwrap_expect = best_practices.get("avoid_unwrap", {})
    if unwrap_expect.get("expect_ratio", 0) < 0.5 and unwrap_expect.get("unwrap_count", 0) > 0:
        recommendations.append({
            "type": "error_safety",
            "priority": "high",
            "message": "Prefer expect() over unwrap() for better error messages",
            "suggestion": "Replace .unwrap() with .expect(\"meaningful message\")"
        })

    # Custom error types
    if patterns.get("result_returns", 0) > 5 and not custom_errors.get("has_custom_errors", False):
        recommendations.append({
            "type": "error_design",
            "priority": "medium",
            "message": "Many Result returns without custom error types",
            "suggestion": "Consider defining custom error types with thiserror"
        })

    # Error documentation
    error_docs = best_practices.get("error_documentation", {})
    if error_docs.get("documentation_ratio", 0) < 0.5:
        recommendations.append({
            "type": "documentation",
            "priority": "low",
            "message": "Error-returning functions lack documentation",
            "suggestion": "Document possible errors in function comments"
        })

    return recommendations


# Score calculation functions

def _calculate_async_quality_score(detection: Dict, error_handling: Dict, performance: Dict) -> int:
    """Calculate async code quality score."""
    score = 100

    # Penalize blocking calls
    blocking_calls = performance.get("blocking_calls", 0)
    score -= blocking_calls * 15

    # Penalize unwrap in async context
    async_unwrap = error_handling.get("async_unwrap", 0)
    score -= async_unwrap * 20

    # Reward proper error handling
    await_question_marks = error_handling.get("await_question_mark", 0)
    total_awaits = detection.get("await_calls", 1)  # Avoid division by zero
    if await_question_marks / total_awaits > 0.7:
        score += 15

    return max(0, min(100, score))


def _calculate_error_handling_score(patterns: Dict, propagation: Dict, best_practices: Dict) -> int:
    """Calculate error handling quality score."""
    score = 100

    # Penalize unwrap usage
    unwrap_count = patterns.get("unwrap_calls", 0)
    score -= min(unwrap_count * 5, 30)

    # Penalize panic usage
    panic_count = patterns.get("panic_calls", 0)
    score -= panic_count * 10

    # Reward question mark usage
    question_marks = patterns.get("question_mark_usage", 0)
    result_returns = patterns.get("result_returns", 1)  # Avoid division by zero
    if question_marks / result_returns > 0.5:
        score += 20

    # Reward error context
    context_ratio = best_practices.get("proper_error_context", {}).get("context_ratio", 0)
    score += int(context_ratio * 15)

    return max(0, min(100, score))


# Formatting functions

def _format_async_analysis_results(analysis: Dict[str, Any]) -> str:
    """Format async analysis results for display."""
    output = []

    output.append("⚡ **Rust Async Analysis**\n")

    # Basic async detection
    detection = analysis.get("detection", {})
    if detection.get("has_async", False):
        output.append("🔄 **Async Patterns:**")
        output.append(f"- Async functions: {detection.get('async_functions', 0)}")
        output.append(f"- Await calls: {detection.get('await_calls', 0)}")
        output.append(f"- Async blocks: {detection.get('async_blocks', 0)}")
        output.append(f"- Future usage: {detection.get('future_usage', 0)}")
        output.append("")

        # Tokio analysis
        tokio = analysis.get("tokio", {})
        if tokio.get("uses_tokio", False):
            output.append("🚀 **Tokio Usage:**")
            output.append(f"- Spawn calls: {tokio.get('spawn_calls', 0)}")
            output.append(f"- Select usage: {tokio.get('select_usage', 0)}")
            output.append(f"- Join operations: {tokio.get('join_usage', 0)}")
            output.append(f"- Sync primitives: {tokio.get('sync_primitive_count', 0)}")
            output.append("")

        # Performance analysis
        performance = analysis.get("performance", {})
        issues = performance.get("potential_issues", [])
        if issues:
            output.append("⚠️ **Performance Issues:**")
            for issue in issues:
                output.append(f"- {issue}")
            output.append("")

        # Async quality score
        async_score = analysis.get("async_score", 0)
        score_emoji = "🟢" if async_score >= 80 else "🟡" if async_score >= 60 else "🔴"
        output.append(f"{score_emoji} **Async Quality Score: {async_score}/100**")

    else:
        output.append("ℹ️ **No async patterns detected in this file**")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("\n💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")
            if rec.get("suggestion"):
                output.append(f"   💡 {rec['suggestion']}")

    return '\n'.join(output)


def _format_error_handling_results(analysis: Dict[str, Any]) -> str:
    """Format error handling analysis results for display."""
    output = []

    output.append("🛡️ **Rust Error Handling Analysis**\n")

    # Basic patterns
    patterns = analysis.get("patterns", {})
    output.append("📊 **Error Patterns:**")
    output.append(f"- Result returns: {patterns.get('result_returns', 0)}")
    output.append(f"- Question mark usage: {patterns.get('question_mark_usage', 0)}")
    output.append(f"- Unwrap calls: {patterns.get('unwrap_calls', 0)}")
    output.append(f"- Expect calls: {patterns.get('expect_calls', 0)}")
    output.append(f"- Panic calls: {patterns.get('panic_calls', 0)}")
    output.append("")

    # Error libraries
    libraries = analysis.get("libraries", {})
    active_libraries = []
    for lib, data in libraries.items():
        if isinstance(data, dict) and data.get("usage", False):
            active_libraries.append(lib)

    if active_libraries:
        output.append(f"📚 **Error Libraries:** {', '.join(active_libraries)}")
        output.append("")

    # Best practices
    best_practices = analysis.get("best_practices", {})
    unwrap_expect = best_practices.get("avoid_unwrap", {})
    if unwrap_expect:
        expect_ratio = unwrap_expect.get("expect_ratio", 0)
        output.append(f"🎯 **Best Practices:**")
        output.append(f"- Expect ratio: {expect_ratio:.1%}")

        error_docs = best_practices.get("error_documentation", {})
        if error_docs:
            doc_ratio = error_docs.get("documentation_ratio", 0)
            output.append(f"- Error documentation: {doc_ratio:.1%}")
        output.append("")

    # Error handling score
    error_score = analysis.get("error_handling_score", 0)
    score_emoji = "🟢" if error_score >= 80 else "🟡" if error_score >= 60 else "🔴"
    output.append(f"{score_emoji} **Error Handling Score: {error_score}/100**")

    # Recommendations
    recommendations = analysis.get("recommendations", [])
    if recommendations:
        output.append("\n💡 **Recommendations:**")
        for rec in recommendations:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec.get("priority"), "⚪")
            output.append(f"{priority_emoji} {rec.get('message', '')}")
            if rec.get("suggestion"):
                output.append(f"   💡 {rec['suggestion']}")

    return '\n'.join(output)


def _format_performance_suggestions(suggestions: List[Dict[str, Any]]) -> str:
    """Format performance suggestions for display."""
    output = []

    output.append("🚀 **Rust Performance Suggestions**\n")

    if not suggestions:
        output.append("✅ No performance improvements identified!")
        return '\n'.join(output)

    # Group by type
    by_type = {}
    for suggestion in suggestions:
        stype = suggestion.get("type", "other")
        if stype not in by_type:
            by_type[stype] = []
        by_type[stype].append(suggestion)

    for suggestion_type, items in by_type.items():
        type_name = suggestion_type.replace('_', ' ').title()
        output.append(f"📝 **{type_name}:**")

        for item in items:
            priority_emoji = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(item.get("priority"), "⚪")
            message = item.get("message", "")
            suggestion = item.get("suggestion", "")
            impact = item.get("impact", "")

            output.append(f"{priority_emoji} {message}")
            output.append(f"   💡 {suggestion}")
            if impact:
                output.append(f"   📈 Impact: {impact}")
            output.append("")

    return '\n'.join(output)