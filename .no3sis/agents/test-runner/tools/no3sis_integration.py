"""
Test Runner Synapse Integration

Connects test-runner to the Synapse knowledge graph for:
- Testing pattern discovery
- Failure solution lookup
- Best practice recommendations
"""

import sys
import asyncio
from pathlib import Path
from typing import Dict, Any, List, Optional

# Import Synapse search functionality
sys.path.append(str(Path.home() / ".no3sis-system" / ".no3sis" / "neo4j"))

try:
    from no3sis_search import search_synapse_context
    from no3sis_health import check_synapse_health
    SYNAPSE_AVAILABLE = True
except ImportError:
    SYNAPSE_AVAILABLE = False
    print("⚠️  Synapse components not available, using mock implementations")


async def search_test_patterns(language: str, test_type: str = "unit") -> Dict[str, Any]:
    """
    Search for testing patterns in the Synapse knowledge graph.

    Args:
        language: Programming language
        test_type: Type of tests (unit, integration, e2e)

    Returns:
        Dict with testing patterns and recommendations
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_test_pattern_search(language, test_type)

    try:
        query = f"testing patterns {language} {test_type} best practices unit test"

        results = search_synapse_context(
            query=query,
            max_results=10,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "patterns": []
            }

        patterns = _extract_patterns_from_results(results, language, test_type)

        return {
            "success": True,
            "language": language,
            "test_type": test_type,
            "patterns": patterns,
            "recommendations": _generate_pattern_recommendations(patterns, language)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error searching test patterns: {e}",
            "patterns": []
        }


async def query_failure_solutions(error_type: str, language: str) -> Dict[str, Any]:
    """
    Query solutions for specific test failure types.

    Args:
        error_type: Type of error (assertion, import, etc.)
        language: Programming language

    Returns:
        Dict with failure solutions and suggestions
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_failure_solution_query(error_type, language)

    try:
        query = f"test failure solution {error_type} {language} debugging fix common error"

        results = search_synapse_context(
            query=query,
            max_results=8,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "solutions": []
            }

        solutions = _extract_solutions_from_results(results, error_type)

        return {
            "success": True,
            "error_type": error_type,
            "language": language,
            "solutions": solutions,
            "quick_fixes": _generate_quick_fixes(solutions, error_type, language)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying failure solutions: {e}",
            "solutions": []
        }


def _extract_patterns_from_results(results: Dict, language: str, test_type: str) -> List[Dict[str, Any]]:
    """Extract testing patterns from search results."""
    patterns = []

    if not results.get("context"):
        return patterns

    for item in results["context"]:
        content = item.get("content", "")

        if any(keyword in content.lower() for keyword in ["test", "pattern", language.lower()]):
            pattern = {
                "content": content[:300] + "..." if len(content) > 300 else content,
                "source": item.get("source", "unknown"),
                "relevance": _calculate_pattern_relevance(content, language, test_type),
                "type": _classify_pattern_type(content)
            }

            patterns.append(pattern)

    # Sort by relevance
    patterns.sort(key=lambda x: x["relevance"], reverse=True)
    return patterns[:5]  # Return top 5


def _extract_solutions_from_results(results: Dict, error_type: str) -> List[Dict[str, Any]]:
    """Extract failure solutions from search results."""
    solutions = []

    if not results.get("context"):
        return solutions

    for item in results["context"]:
        content = item.get("content", "")

        if any(keyword in content.lower() for keyword in [error_type, "error", "fix", "solution"]):
            solution = {
                "content": content,
                "source": item.get("source", "unknown"),
                "applicability": _assess_solution_applicability(content, error_type),
                "steps": _extract_solution_steps(content)
            }

            solutions.append(solution)

    return solutions[:3]  # Return top 3 most applicable


def _calculate_pattern_relevance(content: str, language: str, test_type: str) -> float:
    """Calculate relevance score for testing patterns."""
    score = 0.0
    content_lower = content.lower()

    # Language relevance
    if language.lower() in content_lower:
        score += 2.0

    # Test type relevance
    if test_type in content_lower:
        score += 1.5

    # General test keywords
    test_keywords = ["test", "assert", "mock", "stub", "fixture", "setup"]
    for keyword in test_keywords:
        if keyword in content_lower:
            score += 0.3

    # Code examples boost
    if "```" in content or "def " in content or "function" in content:
        score += 0.5

    return score


def _classify_pattern_type(content: str) -> str:
    """Classify the type of testing pattern."""
    content_lower = content.lower()

    if any(keyword in content_lower for keyword in ["mock", "stub", "fake"]):
        return "mocking"
    elif any(keyword in content_lower for keyword in ["fixture", "setup", "teardown"]):
        return "setup"
    elif any(keyword in content_lower for keyword in ["assert", "expect", "should"]):
        return "assertion"
    elif any(keyword in content_lower for keyword in ["integration", "e2e", "end-to-end"]):
        return "integration"
    else:
        return "general"


def _assess_solution_applicability(content: str, error_type: str) -> float:
    """Assess how applicable a solution is to the error type."""
    score = 0.0
    content_lower = content.lower()

    # Direct error type match
    if error_type.lower() in content_lower:
        score += 3.0

    # Related error terms
    error_synonyms = {
        "assertion": ["assert", "expect", "comparison"],
        "import": ["module", "package", "dependency"],
        "attribute": ["property", "method", "undefined"],
        "null_reference": ["null", "undefined", "none", "nil"]
    }

    synonyms = error_synonyms.get(error_type, [])
    for synonym in synonyms:
        if synonym in content_lower:
            score += 1.0

    # Solution indicators
    if any(keyword in content_lower for keyword in ["fix", "solve", "solution", "resolve"]):
        score += 0.5

    return score


def _extract_solution_steps(content: str) -> List[str]:
    """Extract actionable steps from solution content."""
    steps = []

    # Look for numbered lists
    numbered_steps = re.findall(r'\d+\.\s*(.+)', content)
    steps.extend(numbered_steps)

    # Look for bullet points
    bullet_steps = re.findall(r'[•\-\*]\s*(.+)', content)
    steps.extend(bullet_steps)

    # Look for step-like sentences
    step_sentences = re.findall(r'((?:First|Second|Third|Next|Then|Finally)[^.]+\.)', content)
    steps.extend(step_sentences)

    return steps[:5]  # Return first 5 steps


def _generate_pattern_recommendations(patterns: List[Dict], language: str) -> List[str]:
    """Generate recommendations based on testing patterns."""
    recommendations = []

    pattern_types = [p.get("type", "general") for p in patterns]

    if "mocking" in pattern_types:
        recommendations.append(f"Consider using mocking patterns for {language} tests")

    if "setup" in pattern_types:
        recommendations.append("Implement proper test setup and teardown procedures")

    if "assertion" in pattern_types:
        recommendations.append("Use clear, descriptive assertions in tests")

    if not recommendations:
        recommendations.extend([
            f"Follow {language} testing best practices",
            "Structure tests with clear arrange-act-assert pattern",
            "Use descriptive test names and comments"
        ])

    return recommendations


def _generate_quick_fixes(solutions: List[Dict], error_type: str, language: str) -> List[str]:
    """Generate quick fix suggestions based on solutions."""
    quick_fixes = []

    if error_type == "assertion":
        quick_fixes.extend([
            "Check expected vs actual values in assertions",
            "Verify data types match in comparisons",
            "Add debug prints to see actual values"
        ])
    elif error_type == "import":
        quick_fixes.extend([
            "Verify module/package is installed",
            "Check import path spelling and case",
            "Ensure module is in Python path"
        ])
    elif error_type == "attribute":
        quick_fixes.extend([
            "Check object has the expected attribute",
            "Verify object is properly initialized",
            "Add null/undefined checks before access"
        ])

    # Add solution-specific fixes
    for solution in solutions[:2]:
        steps = solution.get("steps", [])
        for step in steps[:2]:
            if len(step) < 80:  # Keep fixes concise
                quick_fixes.append(step)

    return quick_fixes[:5]


def _mock_test_pattern_search(language: str, test_type: str) -> Dict[str, Any]:
    """Mock test pattern search for development/testing."""
    mock_patterns = [{
        "content": f"Mock testing pattern for {language} {test_type} tests",
        "source": "mock",
        "relevance": 1.0,
        "type": "general"
    }]

    return {
        "success": True,
        "language": language,
        "test_type": test_type,
        "patterns": mock_patterns,
        "recommendations": [f"Use standard {language} testing practices"]
    }


def _mock_failure_solution_query(error_type: str, language: str) -> Dict[str, Any]:
    """Mock failure solution query for development/testing."""
    mock_solutions = [{
        "content": f"Mock solution for {error_type} in {language}",
        "source": "mock",
        "applicability": 1.0,
        "steps": [f"Fix {error_type} error", "Run tests again"]
    }]

    return {
        "success": True,
        "error_type": error_type,
        "language": language,
        "solutions": mock_solutions,
        "quick_fixes": [f"Standard fix for {error_type} errors"]
    }


# Import re module for pattern matching
import re