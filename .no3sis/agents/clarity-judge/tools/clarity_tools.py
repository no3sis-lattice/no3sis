"""
Clarity Judge Tools

Specialized tools for assessing code readability and maintainability.
Provides objective metrics for code clarity evaluation.
"""

import re
import ast
from typing import Dict, Any, List, Tuple, Optional
from pathlib import Path


async def assess_readability(code: str, language: str = "python", context: Dict = None) -> Dict[str, Any]:
    """
    Assess the readability of a code snippet.

    Args:
        code: Source code to assess
        language: Programming language (python, javascript, etc.)
        context: Additional context for assessment

    Returns:
        Dict with clarity score and detailed analysis
    """
    try:
        # Initialize assessment components
        metrics = _calculate_readability_metrics(code, language)
        linguistic_score = _assess_linguistic_clarity(code, language)
        structural_score = _assess_structural_clarity(code, language)
        cognitive_load = _calculate_cognitive_load(code, language)

        # Combine scores with weights
        final_score = (
            linguistic_score * 0.4 +
            structural_score * 0.3 +
            (1.0 - cognitive_load) * 0.3
        )

        # Clamp to valid range
        final_score = max(0.0, min(1.0, final_score))

        return {
            "content": [{
                "type": "text",
                "text": f"Clarity Score: {final_score:.2f} (Linguistic: {linguistic_score:.2f}, Structural: {structural_score:.2f}, Cognitive Load: {cognitive_load:.2f})"
            }],
            "clarity_score": final_score,
            "linguistic_clarity": linguistic_score,
            "structural_clarity": structural_score,
            "cognitive_load": cognitive_load,
            "metrics": metrics,
            "recommendations": _generate_clarity_recommendations(metrics, final_score)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error assessing readability: {e}"
            }],
            "clarity_score": 0.5,  # Default middle score on error
            "error": str(e)
        }


async def compare_clarity(original_code: str, transformed_code: str, language: str = "python") -> Dict[str, Any]:
    """
    Compare clarity between original and transformed code.

    Args:
        original_code: Original code before transformation
        transformed_code: Code after transformation
        language: Programming language

    Returns:
        Dict with comparative clarity analysis
    """
    try:
        # Assess both versions
        original_result = await assess_readability(original_code, language)
        transformed_result = await assess_readability(transformed_code, language)

        original_score = original_result["clarity_score"]
        transformed_score = transformed_result["clarity_score"]

        # Calculate improvement
        clarity_improvement = transformed_score - original_score
        relative_improvement = (
            (clarity_improvement / original_score) * 100
            if original_score > 0 else 0
        )

        # Determine impact
        if clarity_improvement > 0.1:
            impact = "positive"
        elif clarity_improvement < -0.1:
            impact = "negative"
        else:
            impact = "neutral"

        return {
            "content": [{
                "type": "text",
                "text": f"Clarity Comparison: {original_score:.2f} → {transformed_score:.2f} ({impact} impact, {relative_improvement:+.1f}%)"
            }],
            "original_score": original_score,
            "transformed_score": transformed_score,
            "clarity_improvement": clarity_improvement,
            "relative_improvement": relative_improvement,
            "impact": impact,
            "detailed_comparison": _create_detailed_comparison(
                original_result, transformed_result
            )
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error comparing clarity: {e}"
            }],
            "error": str(e)
        }


async def generate_clarity_report(code: str, language: str = "python", include_suggestions: bool = True) -> Dict[str, Any]:
    """
    Generate comprehensive clarity report with actionable recommendations.

    Args:
        code: Source code to analyze
        language: Programming language
        include_suggestions: Whether to include improvement suggestions

    Returns:
        Dict with detailed clarity report
    """
    try:
        # Get base assessment
        assessment = await assess_readability(code, language)

        # Generate detailed report
        report_sections = []

        # Overall Assessment
        score = assessment["clarity_score"]
        if score >= 0.8:
            overall = "Excellent clarity - code is highly readable and maintainable"
        elif score >= 0.6:
            overall = "Good clarity - code is generally readable with minor issues"
        elif score >= 0.4:
            overall = "Moderate clarity - code requires some effort to understand"
        else:
            overall = "Poor clarity - significant readability improvements needed"

        report_sections.append(f"Overall Assessment: {overall}")

        # Metrics Summary
        metrics = assessment.get("metrics", {})
        report_sections.append(f"Lines of Code: {metrics.get('line_count', 0)}")
        report_sections.append(f"Cyclomatic Complexity: {metrics.get('complexity', 0)}")
        report_sections.append(f"Average Line Length: {metrics.get('avg_line_length', 0):.1f}")

        # Improvement Suggestions
        if include_suggestions and score < 0.8:
            suggestions = assessment.get("recommendations", [])
            if suggestions:
                report_sections.append("Improvement Suggestions:")
                for suggestion in suggestions:
                    report_sections.append(f"  • {suggestion}")

        report_text = "\n".join(report_sections)

        return {
            "content": [{
                "type": "text",
                "text": f"Clarity Report:\n{report_text}"
            }],
            "overall_assessment": overall,
            "clarity_score": score,
            "metrics_summary": metrics,
            "improvement_suggestions": assessment.get("recommendations", []),
            "detailed_analysis": assessment
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error generating clarity report: {e}"
            }],
            "error": str(e)
        }


# Private helper functions

def _calculate_readability_metrics(code: str, language: str) -> Dict[str, Any]:
    """Calculate basic readability metrics."""
    lines = code.split('\n')
    non_empty_lines = [line for line in lines if line.strip()]

    metrics = {
        "line_count": len(non_empty_lines),
        "avg_line_length": sum(len(line) for line in non_empty_lines) / len(non_empty_lines) if non_empty_lines else 0,
        "max_line_length": max(len(line) for line in non_empty_lines) if non_empty_lines else 0,
        "comment_ratio": _calculate_comment_ratio(code, language),
        "complexity": _calculate_complexity(code, language),
        "nesting_depth": _calculate_nesting_depth(code),
        "function_count": len(re.findall(r'def\s+\w+|function\s+\w+', code)),
    }

    return metrics


def _assess_linguistic_clarity(code: str, language: str) -> float:
    """Assess clarity based on naming and linguistic factors."""
    score = 1.0

    # Variable naming quality
    variables = re.findall(r'\b[a-z_][a-z0-9_]*\b', code.lower())
    short_names = sum(1 for var in variables if len(var) <= 2 and var not in ['i', 'j', 'k', 'x', 'y', 'z'])
    if variables:
        score -= (short_names / len(variables)) * 0.3

    # Comment quality
    comments = re.findall(r'#.*|//.*|/\*.*?\*/', code)
    meaningful_comments = sum(1 for comment in comments if len(comment.strip()) > 10)
    if comments:
        comment_quality = meaningful_comments / len(comments)
        score = score * (0.7 + comment_quality * 0.3)

    # Identifier descriptiveness
    identifiers = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', code)
    descriptive_ids = sum(1 for ident in identifiers if len(ident) >= 4 and not ident.isupper())
    if identifiers:
        descriptiveness = descriptive_ids / len(identifiers)
        score = score * (0.6 + descriptiveness * 0.4)

    return max(0.0, min(1.0, score))


def _assess_structural_clarity(code: str, language: str) -> float:
    """Assess clarity based on code structure and organization."""
    score = 1.0

    # Line length penalty
    lines = code.split('\n')
    long_lines = sum(1 for line in lines if len(line) > 100)
    if lines:
        score -= (long_lines / len(lines)) * 0.2

    # Nesting depth penalty
    max_depth = _calculate_nesting_depth(code)
    if max_depth > 4:
        score -= (max_depth - 4) * 0.1

    # Function length penalty
    functions = re.split(r'def\s+\w+|function\s+\w+', code)
    long_functions = sum(1 for func in functions if len(func.split('\n')) > 20)
    if functions:
        score -= (long_functions / len(functions)) * 0.15

    # Consistency bonus
    indentation_consistent = _check_indentation_consistency(code)
    if indentation_consistent:
        score += 0.1

    return max(0.0, min(1.0, score))


def _calculate_cognitive_load(code: str, language: str) -> float:
    """Calculate cognitive load (0.0 = low load, 1.0 = high load)."""
    # Base complexity from cyclomatic complexity
    complexity = _calculate_complexity(code, language)
    base_load = min(complexity / 20.0, 1.0)  # Normalize to 0-1

    # Add penalties for cognitive load factors
    penalties = 0.0

    # Deep nesting penalty
    nesting = _calculate_nesting_depth(code)
    penalties += min(nesting / 8.0, 0.3)

    # Long lines penalty
    lines = code.split('\n')
    long_lines = sum(1 for line in lines if len(line) > 120)
    if lines:
        penalties += (long_lines / len(lines)) * 0.2

    # Complex expressions penalty
    complex_patterns = [
        r'.*\?.*:.*\?.*:',  # Nested ternary
        r'\([^)]{50,}\)',   # Long parenthetical expressions
        r'\..*\..*\..*\.',  # Long method chains
    ]

    for pattern in complex_patterns:
        matches = len(re.findall(pattern, code))
        penalties += min(matches * 0.05, 0.1)

    total_load = base_load + penalties
    return max(0.0, min(1.0, total_load))


def _calculate_comment_ratio(code: str, language: str) -> float:
    """Calculate ratio of comment lines to code lines."""
    lines = code.split('\n')
    comment_patterns = {
        "python": r'^\s*#',
        "javascript": r'^\s*(//|/\*)',
        "typescript": r'^\s*(//|/\*)',
    }

    pattern = comment_patterns.get(language, r'^\s*(//|#)')
    comment_lines = sum(1 for line in lines if re.match(pattern, line))
    code_lines = sum(1 for line in lines if line.strip() and not re.match(pattern, line))

    return comment_lines / max(code_lines, 1)


def _calculate_complexity(code: str, language: str) -> int:
    """Calculate cyclomatic complexity."""
    if language == "python":
        return _python_complexity(code)
    else:
        return _generic_complexity(code)


def _python_complexity(code: str) -> int:
    """Calculate Python cyclomatic complexity."""
    try:
        tree = ast.parse(code)
        complexity = 1  # Base complexity

        for node in ast.walk(tree):
            if isinstance(node, (ast.If, ast.While, ast.For, ast.AsyncFor)):
                complexity += 1
            elif isinstance(node, ast.ExceptHandler):
                complexity += 1
            elif isinstance(node, ast.BoolOp):
                complexity += len(node.values) - 1

        return complexity
    except:
        return _generic_complexity(code)


def _generic_complexity(code: str) -> int:
    """Calculate generic complexity for any language."""
    decision_keywords = ['if', 'elif', 'else', 'while', 'for', 'switch', 'case', 'catch', 'and', 'or', '&&', '||']
    complexity = 1

    for keyword in decision_keywords:
        complexity += len(re.findall(rf'\b{keyword}\b', code, re.IGNORECASE))

    return complexity


def _calculate_nesting_depth(code: str) -> int:
    """Calculate maximum nesting depth."""
    lines = code.split('\n')
    max_depth = 0
    current_depth = 0

    for line in lines:
        stripped = line.lstrip()
        if not stripped or stripped.startswith('#') or stripped.startswith('//'):
            continue

        # Calculate indentation level (assuming 4-space or 1-tab indents)
        indent_chars = len(line) - len(stripped)
        if '\t' in line[:indent_chars]:
            level = line[:indent_chars].count('\t')
        else:
            level = indent_chars // 4

        # Track control structures that increase nesting
        if any(keyword in stripped for keyword in ['if ', 'for ', 'while ', 'def ', 'class ', 'function ', 'try:']):
            current_depth = level + 1
            max_depth = max(max_depth, current_depth)
        else:
            current_depth = level

    return max_depth


def _check_indentation_consistency(code: str) -> bool:
    """Check if indentation is consistent throughout the code."""
    lines = code.split('\n')
    indentation_types = set()

    for line in lines:
        if line.strip():  # Skip empty lines
            leading = line[:len(line) - len(line.lstrip())]
            if leading:
                if '\t' in leading:
                    indentation_types.add('tab')
                if ' ' in leading:
                    indentation_types.add('space')

    return len(indentation_types) <= 1  # Consistent if only one type or no indentation


def _generate_clarity_recommendations(metrics: Dict[str, Any], score: float) -> List[str]:
    """Generate actionable recommendations for improving clarity."""
    recommendations = []

    if score < 0.8:
        if metrics.get("avg_line_length", 0) > 100:
            recommendations.append("Consider breaking long lines for better readability")

        if metrics.get("nesting_depth", 0) > 4:
            recommendations.append("Reduce nesting depth by extracting functions or using early returns")

        if metrics.get("complexity", 0) > 10:
            recommendations.append("Break down complex functions into smaller, single-purpose functions")

        if metrics.get("comment_ratio", 0) < 0.1:
            recommendations.append("Add meaningful comments to explain complex logic")

        # Function-specific recommendations
        if metrics.get("line_count", 0) > 50:
            recommendations.append("Consider splitting large code blocks into smaller functions")

    return recommendations


def _create_detailed_comparison(original_result: Dict, transformed_result: Dict) -> Dict[str, Any]:
    """Create detailed comparison between original and transformed code assessments."""
    return {
        "linguistic_clarity": {
            "original": original_result.get("linguistic_clarity", 0.0),
            "transformed": transformed_result.get("linguistic_clarity", 0.0),
            "change": transformed_result.get("linguistic_clarity", 0.0) - original_result.get("linguistic_clarity", 0.0)
        },
        "structural_clarity": {
            "original": original_result.get("structural_clarity", 0.0),
            "transformed": transformed_result.get("structural_clarity", 0.0),
            "change": transformed_result.get("structural_clarity", 0.0) - original_result.get("structural_clarity", 0.0)
        },
        "cognitive_load": {
            "original": original_result.get("cognitive_load", 0.0),
            "transformed": transformed_result.get("cognitive_load", 0.0),
            "change": transformed_result.get("cognitive_load", 0.0) - original_result.get("cognitive_load", 0.0)
        }
    }