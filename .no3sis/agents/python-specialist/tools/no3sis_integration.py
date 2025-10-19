"""
Python Specialist Synapse Integration

Connects python-specialist to the Synapse knowledge graph for:
- Python-specific pattern discovery
- Best practice retrieval
- Framework and library recommendations
"""

import sys
import asyncio
from pathlib import Path
from typing import Dict, Any, List, Optional

# Import Synapse search functionality
sys.path.append(str(Path.home() / ".no3sis-system" / ".no3sis" / "neo4j"))

try:
    from no3sis_search import search_synapse_context
    SYNAPSE_AVAILABLE = True
except ImportError:
    SYNAPSE_AVAILABLE = False
    print("⚠️  Synapse components not available, using mock implementations")


async def query_python_patterns(pattern_type: str, context: str = "") -> Dict[str, Any]:
    """
    Search for Python patterns in the Synapse knowledge graph.

    Args:
        pattern_type: Type of pattern (async, testing, performance, etc.)
        context: Additional context for the search

    Returns:
        Dict with Python patterns and recommendations
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_python_pattern_search(pattern_type, context)

    try:
        query = f"python pattern {pattern_type} {context} best practice idiom"

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

        patterns = _extract_python_patterns_from_results(results, pattern_type)

        return {
            "success": True,
            "pattern_type": pattern_type,
            "patterns": patterns,
            "recommendations": _generate_python_recommendations(patterns, pattern_type)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying Python patterns: {e}",
            "patterns": []
        }


async def search_python_standards(standard_type: str, language_version: str = "3.10+") -> Dict[str, Any]:
    """
    Search for Python coding standards and conventions.

    Args:
        standard_type: Type of standard (pep8, typing, testing, etc.)
        language_version: Python version context

    Returns:
        Dict with Python standards and guidelines
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_python_standards_search(standard_type, language_version)

    try:
        query = f"python standard {standard_type} {language_version} pep convention guideline"

        results = search_synapse_context(
            query=query,
            max_results=8,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "standards": []
            }

        standards = _extract_standards_from_results(results, standard_type)

        return {
            "success": True,
            "standard_type": standard_type,
            "language_version": language_version,
            "standards": standards,
            "guidelines": _generate_standard_guidelines(standards, standard_type)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error searching Python standards: {e}",
            "standards": []
        }


def _extract_python_patterns_from_results(results: Dict, pattern_type: str) -> List[Dict[str, Any]]:
    """Extract Python patterns from search results."""
    patterns = []

    if not results.get("context"):
        return patterns

    for item in results["context"]:
        content = item.get("content", "")

        if any(keyword in content.lower() for keyword in ["python", pattern_type, "def ", "class ", "import"]):
            pattern = {
                "content": content[:500] + "..." if len(content) > 500 else content,
                "source": item.get("source", "unknown"),
                "relevance": _calculate_python_pattern_relevance(content, pattern_type),
                "category": _classify_python_pattern(content, pattern_type)
            }

            patterns.append(pattern)

    # Sort by relevance
    patterns.sort(key=lambda x: x["relevance"], reverse=True)
    return patterns[:5]  # Return top 5


def _extract_standards_from_results(results: Dict, standard_type: str) -> List[Dict[str, Any]]:
    """Extract Python standards from search results."""
    standards = []

    if not results.get("context"):
        return standards

    for item in results["context"]:
        content = item.get("content", "")

        if any(keyword in content.lower() for keyword in [standard_type, "pep", "standard", "convention", "guideline"]):
            standard = {
                "content": content,
                "source": item.get("source", "unknown"),
                "applicability": _assess_standard_applicability(content, standard_type),
                "rules": _extract_standard_rules(content)
            }

            standards.append(standard)

    return standards[:3]  # Return top 3 most applicable


def _calculate_python_pattern_relevance(content: str, pattern_type: str) -> float:
    """Calculate relevance score for Python patterns."""
    score = 0.0
    content_lower = content.lower()

    # Pattern type relevance
    if pattern_type in content_lower:
        score += 2.0

    # Python-specific keywords
    python_keywords = ["def", "class", "import", "async", "await", "yield", "with"]
    for keyword in python_keywords:
        if keyword in content_lower:
            score += 0.3

    # Modern Python features
    modern_features = ["type hints", "dataclass", "pathlib", "f-string", "match case"]
    for feature in modern_features:
        if feature in content_lower:
            score += 0.5

    # Code examples boost
    if "```python" in content or ">>>" in content:
        score += 0.8

    # Framework-specific patterns
    frameworks = ["fastapi", "django", "flask", "pytest", "asyncio", "pandas"]
    for framework in frameworks:
        if framework in content_lower:
            score += 0.4

    return score


def _classify_python_pattern(content: str, pattern_type: str) -> str:
    """Classify the type of Python pattern."""
    content_lower = content.lower()

    if any(keyword in content_lower for keyword in ["async", "await", "asyncio"]):
        return "async"
    elif any(keyword in content_lower for keyword in ["test", "pytest", "unittest", "mock"]):
        return "testing"
    elif any(keyword in content_lower for keyword in ["performance", "optimization", "speed"]):
        return "performance"
    elif any(keyword in content_lower for keyword in ["dataclass", "typing", "type", "annotation"]):
        return "typing"
    elif any(keyword in content_lower for keyword in ["error", "exception", "try", "except"]):
        return "error_handling"
    else:
        return "general"


def _assess_standard_applicability(content: str, standard_type: str) -> float:
    """Assess how applicable a standard is to the specified type."""
    score = 0.0
    content_lower = content.lower()

    # Direct standard type match
    if standard_type.lower() in content_lower:
        score += 3.0

    # Related terms
    standard_terms = {
        "pep8": ["formatting", "style", "naming", "whitespace"],
        "typing": ["type", "annotation", "mypy", "protocol"],
        "testing": ["test", "coverage", "mock", "fixture"],
        "documentation": ["docstring", "sphinx", "comment"]
    }

    terms = standard_terms.get(standard_type, [])
    for term in terms:
        if term in content_lower:
            score += 1.0

    # Authority indicators
    if any(indicator in content_lower for indicator in ["pep", "python.org", "official", "standard"]):
        score += 0.5

    return score


def _extract_standard_rules(content: str) -> List[str]:
    """Extract specific rules from standard content."""
    rules = []

    # Look for numbered rules
    numbered_rules = re.findall(r'\d+\.\s*(.+)', content)
    rules.extend(numbered_rules[:5])  # First 5

    # Look for bullet points
    bullet_rules = re.findall(r'[•\-\*]\s*(.+)', content)
    rules.extend(bullet_rules[:5])  # First 5

    # Look for "should/must" statements
    should_rules = re.findall(r'(.*(?:should|must|shall)[^.]+\.)', content, re.IGNORECASE)
    rules.extend(should_rules[:3])  # First 3

    return rules[:10]  # Total max 10 rules


def _generate_python_recommendations(patterns: List[Dict], pattern_type: str) -> List[str]:
    """Generate recommendations based on Python patterns."""
    recommendations = []

    if not patterns:
        recommendations.extend(_get_default_python_recommendations(pattern_type))
        return recommendations

    # Analyze pattern categories
    categories = [p.get("category", "general") for p in patterns]
    category_counts = {cat: categories.count(cat) for cat in set(categories)}

    if category_counts.get("async", 0) > 0:
        recommendations.append("Consider using async/await patterns for I/O operations")

    if category_counts.get("typing", 0) > 0:
        recommendations.append("Add type hints to improve code clarity and catch errors")

    if category_counts.get("testing", 0) > 0:
        recommendations.append("Implement comprehensive test coverage with pytest")

    if category_counts.get("performance", 0) > 0:
        recommendations.append("Profile code and optimize bottlenecks")

    # Add pattern-specific recommendations
    pattern_recommendations = {
        "async": ["Use asyncio.gather() for concurrent operations", "Avoid blocking calls in async functions"],
        "testing": ["Use fixtures for test setup", "Mock external dependencies"],
        "performance": ["Use list comprehensions over loops", "Consider NumPy for numerical operations"],
        "error_handling": ["Use specific exception types", "Implement proper cleanup with context managers"]
    }

    recommendations.extend(pattern_recommendations.get(pattern_type, []))

    return recommendations[:5]  # Limit to 5 recommendations


def _generate_standard_guidelines(standards: List[Dict], standard_type: str) -> List[str]:
    """Generate guidelines based on standards."""
    guidelines = []

    for standard in standards[:2]:  # Use first 2 standards
        rules = standard.get("rules", [])
        guidelines.extend(rules[:3])  # First 3 rules from each

    if not guidelines:
        guidelines.extend(_get_default_guidelines(standard_type))

    return guidelines[:8]  # Max 8 guidelines


def _get_default_python_recommendations(pattern_type: str) -> List[str]:
    """Get default recommendations when no patterns found."""
    defaults = {
        "async": [
            "Use async/await for I/O-bound operations",
            "Avoid blocking calls in async functions",
            "Use aiohttp for async HTTP requests"
        ],
        "testing": [
            "Write tests for all public functions",
            "Use pytest as the test framework",
            "Mock external dependencies"
        ],
        "performance": [
            "Profile before optimizing",
            "Use appropriate data structures",
            "Consider NumPy for numerical operations"
        ],
        "typing": [
            "Add type hints to function signatures",
            "Use modern typing features",
            "Run mypy for type checking"
        ]
    }

    return defaults.get(pattern_type, ["Follow Python best practices"])


def _get_default_guidelines(standard_type: str) -> List[str]:
    """Get default guidelines when no standards found."""
    defaults = {
        "pep8": [
            "Use snake_case for variables and functions",
            "Use PascalCase for classes",
            "Limit lines to 88 characters",
            "Use 4 spaces for indentation"
        ],
        "typing": [
            "Add type hints to all function signatures",
            "Use Union and Optional where appropriate",
            "Import types from typing module"
        ],
        "testing": [
            "Write descriptive test names",
            "Use arrange-act-assert pattern",
            "Aim for high test coverage"
        ]
    }

    return defaults.get(standard_type, ["Follow established Python conventions"])


def _mock_python_pattern_search(pattern_type: str, context: str) -> Dict[str, Any]:
    """Mock Python pattern search for development/testing."""
    mock_patterns = [{
        "content": f"Mock Python pattern for {pattern_type}",
        "source": "mock",
        "relevance": 1.0,
        "category": pattern_type
    }]

    return {
        "success": True,
        "pattern_type": pattern_type,
        "patterns": mock_patterns,
        "recommendations": [f"Use standard {pattern_type} patterns in Python"]
    }


def _mock_python_standards_search(standard_type: str, language_version: str) -> Dict[str, Any]:
    """Mock Python standards search for development/testing."""
    mock_standards = [{
        "content": f"Mock Python standard for {standard_type}",
        "source": "mock",
        "applicability": 1.0,
        "rules": [f"Follow {standard_type} guidelines"]
    }]

    return {
        "success": True,
        "standard_type": standard_type,
        "language_version": language_version,
        "standards": mock_standards,
        "guidelines": [f"Apply {standard_type} standards to Python code"]
    }


# Import re for pattern matching
import re