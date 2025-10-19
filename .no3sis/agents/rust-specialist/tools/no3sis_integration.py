"""
Rust Specialist Synapse Integration

Connects rust-specialist to the Synapse knowledge graph for:
- Rust-specific pattern discovery (ownership, async, performance)
- Best practice retrieval for the Rust ecosystem
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


async def query_rust_patterns(pattern_type: str, context: str = "") -> Dict[str, Any]:
    """
    Search for Rust patterns in the Synapse knowledge graph.

    Args:
        pattern_type: Type of pattern (ownership, async, performance, error-handling, etc.)
        context: Additional context for the search

    Returns:
        Dict with Rust patterns and recommendations
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_rust_pattern_search(pattern_type, context)

    try:
        query = f"rust pattern {pattern_type} {context} ownership borrowing best practice idiom"

        results = search_synapse_context(
            query=query,
            max_results=12,  # More results for Rust complexity
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "patterns": []
            }

        patterns = _extract_rust_patterns_from_results(results, pattern_type)

        return {
            "success": True,
            "pattern_type": pattern_type,
            "patterns": patterns,
            "recommendations": _generate_rust_recommendations(patterns, pattern_type)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying Rust patterns: {e}",
            "patterns": []
        }


async def search_rust_standards(standard_type: str, domain: str = "general") -> Dict[str, Any]:
    """
    Search for Rust coding standards and conventions.

    Args:
        standard_type: Type of standard (clippy, cargo, testing, async, etc.)
        domain: Domain context (web, systems, embedded, cli)

    Returns:
        Dict with Rust standards and guidelines
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_rust_standards_search(standard_type, domain)

    try:
        query = f"rust standard {standard_type} {domain} clippy cargo convention guideline best practice"

        results = search_synapse_context(
            query=query,
            max_results=10,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "standards": []
            }

        standards = _extract_rust_standards_from_results(results, standard_type, domain)

        return {
            "success": True,
            "standard_type": standard_type,
            "domain": domain,
            "standards": standards,
            "recommendations": _generate_standards_recommendations(standards, standard_type, domain)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying Rust standards: {e}",
            "standards": []
        }


def _extract_rust_patterns_from_results(results: Dict[str, Any], pattern_type: str) -> List[Dict[str, Any]]:
    """Extract Rust patterns from Synapse search results."""
    patterns = []

    context = results.get("context", {})
    primary_matches = context.get("primary_matches", [])

    for match in primary_matches[:10]:  # Limit to top 10 matches
        pattern_entry = {
            "title": match.get("title", "Rust Pattern"),
            "description": match.get("snippet", "")[:300] + "..." if len(match.get("snippet", "")) > 300 else match.get("snippet", ""),
            "source": match.get("source", "Unknown"),
            "relevance_score": match.get("score", 0.0),
            "pattern_category": _categorize_rust_pattern(match.get("content", ""), pattern_type),
            "complexity_level": _assess_pattern_complexity(match.get("content", ""), pattern_type)
        }

        # Extract code examples if available
        content = match.get("content", "")
        code_examples = _extract_rust_code_examples(content)
        if code_examples:
            pattern_entry["examples"] = code_examples[:3]  # Limit to 3 examples

        # Extract ownership-specific information
        if pattern_type in ["ownership", "borrowing", "lifetimes"]:
            pattern_entry["ownership_insights"] = _extract_ownership_insights(content)

        patterns.append(pattern_entry)

    return patterns


def _extract_rust_standards_from_results(results: Dict[str, Any], standard_type: str, domain: str) -> List[Dict[str, Any]]:
    """Extract Rust standards from Synapse search results."""
    standards = []

    context = results.get("context", {})
    primary_matches = context.get("primary_matches", [])

    for match in primary_matches[:8]:  # Limit to top 8 matches
        standard_entry = {
            "title": match.get("title", "Rust Standard"),
            "description": match.get("snippet", "")[:200] + "..." if len(match.get("snippet", "")) > 200 else match.get("snippet", ""),
            "source": match.get("source", "Unknown"),
            "standard_category": _categorize_rust_standard(match.get("content", ""), standard_type),
            "domain_specific": domain != "general",
            "enforcement_level": _assess_enforcement_level(match.get("content", ""), standard_type)
        }

        # Extract configuration examples
        content = match.get("content", "")
        config_examples = _extract_rust_config_examples(content, standard_type)
        if config_examples:
            standard_entry["configuration"] = config_examples

        # Extract clippy-specific information
        if standard_type == "clippy":
            standard_entry["clippy_rules"] = _extract_clippy_rules(content)

        standards.append(standard_entry)

    return standards


def _categorize_rust_pattern(content: str, pattern_type: str) -> str:
    """Categorize the Rust pattern based on content analysis."""
    content_lower = content.lower()

    # Ownership and borrowing categorization
    if pattern_type == "ownership":
        if "move" in content_lower and "semantic" in content_lower:
            return "Move Semantics"
        elif "borrow" in content_lower and "checker" in content_lower:
            return "Borrow Checker"
        elif "smart" in content_lower and "pointer" in content_lower:
            return "Smart Pointers"
        elif "lifetime" in content_lower:
            return "Lifetime Management"
        else:
            return "Ownership General"

    elif pattern_type == "async":
        if "tokio" in content_lower:
            return "Tokio Patterns"
        elif "future" in content_lower or "poll" in content_lower:
            return "Future Composition"
        elif "stream" in content_lower:
            return "Stream Processing"
        elif "spawn" in content_lower or "task" in content_lower:
            return "Task Management"
        else:
            return "Async General"

    elif pattern_type == "error-handling":
        if "result" in content_lower and "chain" in content_lower:
            return "Result Chaining"
        elif "custom" in content_lower and "error" in content_lower:
            return "Custom Error Types"
        elif "anyhow" in content_lower or "thiserror" in content_lower:
            return "Error Libraries"
        elif "propagat" in content_lower:
            return "Error Propagation"
        else:
            return "Error Handling General"

    elif pattern_type == "performance":
        if "zero" in content_lower and "cost" in content_lower:
            return "Zero-Cost Abstractions"
        elif "allocation" in content_lower or "memory" in content_lower:
            return "Memory Optimization"
        elif "iterator" in content_lower or "lazy" in content_lower:
            return "Iterator Optimization"
        elif "simd" in content_lower or "vectoriz" in content_lower:
            return "SIMD Optimization"
        else:
            return "Performance General"

    elif pattern_type == "testing":
        if "property" in content_lower or "proptest" in content_lower:
            return "Property Testing"
        elif "mock" in content_lower:
            return "Mocking Patterns"
        elif "integration" in content_lower:
            return "Integration Testing"
        elif "benchmark" in content_lower:
            return "Benchmarking"
        else:
            return "Testing General"

    return "General Pattern"


def _categorize_rust_standard(content: str, standard_type: str) -> str:
    """Categorize the Rust standard based on content analysis."""
    content_lower = content.lower()

    if standard_type == "clippy":
        if "pedantic" in content_lower:
            return "Clippy Pedantic Rules"
        elif "nursery" in content_lower:
            return "Clippy Nursery Rules"
        elif "restriction" in content_lower:
            return "Clippy Restriction Rules"
        else:
            return "Clippy Default Rules"

    elif standard_type == "cargo":
        if "workspace" in content_lower:
            return "Cargo Workspace Standards"
        elif "feature" in content_lower:
            return "Cargo Feature Standards"
        elif "profile" in content_lower:
            return "Cargo Profile Standards"
        else:
            return "Cargo General Standards"

    elif standard_type == "testing":
        if "unit" in content_lower:
            return "Unit Test Standards"
        elif "integration" in content_lower:
            return "Integration Test Standards"
        elif "doc" in content_lower:
            return "Documentation Test Standards"
        else:
            return "Testing General Standards"

    elif standard_type == "async":
        if "tokio" in content_lower:
            return "Tokio Standards"
        elif "runtime" in content_lower:
            return "Async Runtime Standards"
        else:
            return "Async General Standards"

    return "General Standard"


def _assess_pattern_complexity(content: str, pattern_type: str) -> str:
    """Assess the complexity level of a pattern."""
    content_lower = content.lower()

    # Complexity indicators
    complex_keywords = [
        "lifetime", "generic", "trait", "associated", "const", "macro",
        "unsafe", "phantom", "higher-rank", "variance"
    ]

    medium_keywords = [
        "borrow", "ownership", "async", "future", "closure", "iterator"
    ]

    complex_count = sum(1 for keyword in complex_keywords if keyword in content_lower)
    medium_count = sum(1 for keyword in medium_keywords if keyword in content_lower)

    if complex_count >= 2:
        return "Advanced"
    elif complex_count >= 1 or medium_count >= 3:
        return "Intermediate"
    else:
        return "Beginner"


def _assess_enforcement_level(content: str, standard_type: str) -> str:
    """Assess the enforcement level of a standard."""
    content_lower = content.lower()

    if "must" in content_lower or "required" in content_lower or "error" in content_lower:
        return "Required"
    elif "should" in content_lower or "recommend" in content_lower or "warn" in content_lower:
        return "Recommended"
    elif "consider" in content_lower or "suggest" in content_lower:
        return "Optional"
    else:
        return "Informational"


def _extract_rust_code_examples(content: str) -> List[str]:
    """Extract Rust code examples from content."""
    import re

    # Look for Rust code blocks
    rust_patterns = [
        r'```rust\n(.*?)\n```',
        r'```\n(.*?)\n```',  # Generic code blocks
        r'`([^`]{30,})`'     # Long inline code
    ]

    examples = []
    for pattern in rust_patterns:
        matches = re.findall(pattern, content, re.MULTILINE | re.DOTALL)
        for match in matches:
            code = match.strip()
            # Check if it looks like Rust code
            if any(keyword in code for keyword in ['fn ', 'let ', 'struct ', 'enum ', 'impl ', 'use ', 'mod ']):
                examples.append(code[:400] + "..." if len(code) > 400 else code)

    return examples[:4]  # Return up to 4 examples


def _extract_ownership_insights(content: str) -> Dict[str, Any]:
    """Extract ownership-specific insights from content."""
    content_lower = content.lower()

    insights = {
        "involves_moves": "move" in content_lower,
        "involves_borrowing": "borrow" in content_lower,
        "involves_lifetimes": "lifetime" in content_lower,
        "involves_smart_pointers": any(sp in content_lower for sp in ["box", "rc", "arc", "refcell"]),
        "memory_safety_focus": "memory" in content_lower and "safety" in content_lower
    }

    return insights


def _extract_rust_config_examples(content: str, standard_type: str) -> Optional[str]:
    """Extract configuration examples based on standard type."""
    import re

    if standard_type == "clippy":
        # Look for Clippy configuration
        clippy_patterns = [
            r'clippy\.toml.*?\n(.*?)(?:\n\n|\n$)',
            r'\[lints\.clippy\](.*?)(?:\n\[|\n$)',
            r'clippy.*?=.*?{([^}]+)}'
        ]
        for pattern in clippy_patterns:
            matches = re.findall(pattern, content, re.DOTALL | re.IGNORECASE)
            if matches:
                return matches[0][:500]  # Limit to 500 chars

    elif standard_type == "cargo":
        # Look for Cargo.toml configuration
        cargo_patterns = [
            r'\[profile\..*?\](.*?)(?:\n\[|\n$)',
            r'\[workspace\](.*?)(?:\n\[|\n$)',
            r'Cargo\.toml.*?\n(.*?)(?:\n\n|\n$)'
        ]
        for pattern in cargo_patterns:
            matches = re.findall(pattern, content, re.DOTALL | re.IGNORECASE)
            if matches:
                return matches[0][:500]

    return None


def _extract_clippy_rules(content: str) -> List[str]:
    """Extract specific Clippy rules from content."""
    import re

    # Look for clippy rule names
    rule_pattern = r'clippy::([a-z_]+)'
    rules = re.findall(rule_pattern, content.lower())

    # Remove duplicates and limit
    return list(set(rules))[:10]


def _generate_rust_recommendations(patterns: List[Dict], pattern_type: str) -> List[Dict[str, Any]]:
    """Generate recommendations based on discovered Rust patterns."""
    recommendations = []

    if not patterns:
        return [{
            "type": "no_patterns",
            "message": f"No specific {pattern_type} patterns found in knowledge base",
            "suggestion": "Consider checking official Rust documentation or The Rust Book"
        }]

    # Complexity-based recommendations
    complexity_levels = [p.get("complexity_level", "Beginner") for p in patterns]
    advanced_count = complexity_levels.count("Advanced")
    intermediate_count = complexity_levels.count("Intermediate")

    if advanced_count >= 3:
        recommendations.append({
            "type": "complexity_warning",
            "priority": "medium",
            "message": f"{advanced_count} advanced {pattern_type} patterns found",
            "suggestion": "Consider starting with intermediate patterns before tackling advanced ones",
            "patterns": [p["title"] for p in patterns if p.get("complexity_level") == "Advanced"][:3]
        })

    # Category clustering
    categories = {}
    for pattern in patterns:
        category = pattern.get("pattern_category", "General")
        if category not in categories:
            categories[category] = []
        categories[category].append(pattern)

    for category, category_patterns in categories.items():
        if len(category_patterns) >= 3:
            recommendations.append({
                "type": "pattern_cluster",
                "category": category,
                "message": f"Multiple {category} patterns available",
                "suggestion": f"Review {len(category_patterns)} {category} patterns for comprehensive understanding",
                "pattern_count": len(category_patterns)
            })

    # High relevance recommendations
    high_relevance = [p for p in patterns if p.get("relevance_score", 0) > 0.8]
    if high_relevance:
        recommendations.append({
            "type": "high_relevance",
            "message": f"{len(high_relevance)} highly relevant patterns found",
            "suggestion": "Prioritize implementing these well-matched patterns first",
            "patterns": [p["title"] for p in high_relevance[:3]]
        })

    # Ownership-specific recommendations
    if pattern_type == "ownership":
        ownership_insights = [p.get("ownership_insights", {}) for p in patterns]
        if any(insight.get("involves_lifetimes", False) for insight in ownership_insights):
            recommendations.append({
                "type": "lifetime_complexity",
                "message": "Lifetime annotations found in patterns",
                "suggestion": "Study lifetime concepts thoroughly before implementing these patterns"
            })

    return recommendations


def _generate_standards_recommendations(standards: List[Dict], standard_type: str, domain: str) -> List[Dict[str, Any]]:
    """Generate recommendations based on discovered Rust standards."""
    recommendations = []

    if not standards:
        return [{
            "type": "no_standards",
            "message": f"No specific {standard_type} standards found for {domain}",
            "suggestion": "Consider using general Rust standards or community best practices"
        }]

    # Enforcement level recommendations
    enforcement_levels = [s.get("enforcement_level", "Informational") for s in standards]
    required_count = enforcement_levels.count("Required")
    recommended_count = enforcement_levels.count("Recommended")

    if required_count > 0:
        recommendations.append({
            "type": "required_standards",
            "priority": "high",
            "message": f"{required_count} required standards found",
            "suggestion": "Implement required standards first to ensure compliance",
            "standards": [s["title"] for s in standards if s.get("enforcement_level") == "Required"][:3]
        })

    if recommended_count > 0:
        recommendations.append({
            "type": "recommended_standards",
            "priority": "medium",
            "message": f"{recommended_count} recommended standards found",
            "suggestion": "Consider implementing recommended standards for better code quality",
            "standards": [s["title"] for s in standards if s.get("enforcement_level") == "Recommended"][:3]
        })

    # Domain-specific recommendations
    domain_specific = [s for s in standards if s.get("domain_specific", False)]
    if domain_specific:
        recommendations.append({
            "type": "domain_specific",
            "message": f"{len(domain_specific)} {domain}-specific standards found",
            "suggestion": f"Apply these {domain} optimizations for better integration",
            "standards": [s["title"] for s in domain_specific[:3]]
        })

    # Configuration recommendations
    with_config = [s for s in standards if "configuration" in s]
    if with_config:
        recommendations.append({
            "type": "configuration_available",
            "message": f"{len(with_config)} standards include configuration examples",
            "suggestion": "Use these configuration examples as starting points",
            "configurable_standards": [s["title"] for s in with_config]
        })

    return recommendations


# Mock implementations for development/testing

def _mock_rust_pattern_search(pattern_type: str, context: str) -> Dict[str, Any]:
    """Mock Rust pattern search for development."""

    mock_patterns = {
        "ownership": [
            {
                "title": "RAII Pattern in Rust",
                "description": "Resource Acquisition Is Initialization pattern ensures resources are properly cleaned up using Rust's ownership system.",
                "source": "Mock Rust Guide",
                "relevance_score": 0.95,
                "pattern_category": "Ownership General",
                "complexity_level": "Intermediate",
                "ownership_insights": {
                    "involves_moves": True,
                    "involves_borrowing": True,
                    "memory_safety_focus": True
                },
                "examples": [
                    "struct FileHandle { file: File } impl Drop for FileHandle { fn drop(&mut self) { ... } }"
                ]
            },
            {
                "title": "Smart Pointer Patterns with Arc and Mutex",
                "description": "Thread-safe shared ownership using Arc<Mutex<T>> for concurrent access to data.",
                "source": "Mock Concurrency Patterns",
                "relevance_score": 0.88,
                "pattern_category": "Smart Pointers",
                "complexity_level": "Advanced",
                "examples": [
                    "let shared_data = Arc::new(Mutex::new(data)); let clone = Arc::clone(&shared_data);"
                ]
            }
        ],
        "async": [
            {
                "title": "Tokio Runtime Patterns",
                "description": "Best practices for setting up and using Tokio runtime for async applications.",
                "source": "Mock Tokio Guide",
                "relevance_score": 0.92,
                "pattern_category": "Tokio Patterns",
                "complexity_level": "Intermediate",
                "examples": [
                    "#[tokio::main] async fn main() { let result = tokio::spawn(async_task()).await?; }"
                ]
            }
        ],
        "performance": [
            {
                "title": "Zero-Cost Abstractions in Practice",
                "description": "How to leverage Rust's zero-cost abstractions for optimal performance without sacrificing safety.",
                "source": "Mock Performance Guide",
                "relevance_score": 0.85,
                "pattern_category": "Zero-Cost Abstractions",
                "complexity_level": "Advanced",
                "examples": [
                    "fn generic_function<T: Iterator<Item = u32>>(iter: T) -> u32 { iter.sum() }"
                ]
            }
        ]
    }

    patterns = mock_patterns.get(pattern_type, [
        {
            "title": f"Rust {pattern_type.title()} Pattern",
            "description": f"General Rust patterns for {pattern_type} development.",
            "source": "Mock Rust Patterns",
            "relevance_score": 0.7,
            "pattern_category": "General Pattern",
            "complexity_level": "Intermediate"
        }
    ])

    return {
        "success": True,
        "pattern_type": pattern_type,
        "patterns": patterns,
        "recommendations": _generate_rust_recommendations(patterns, pattern_type)
    }


def _mock_rust_standards_search(standard_type: str, domain: str) -> Dict[str, Any]:
    """Mock Rust standards search for development."""

    mock_standards = {
        "clippy": [
            {
                "title": "Comprehensive Clippy Configuration",
                "description": "Recommended Clippy lints for production Rust projects with balanced strictness.",
                "source": "Mock Clippy Guide",
                "standard_category": "Clippy Default Rules",
                "enforcement_level": "Recommended",
                "domain_specific": domain != "general",
                "configuration": 'all = "warn"\npedantic = "warn"\nnursery = "warn"',
                "clippy_rules": ["needless_pass_by_value", "too_many_arguments", "cognitive_complexity"]
            }
        ],
        "cargo": [
            {
                "title": "Optimized Cargo Profile Settings",
                "description": "Performance-focused Cargo.toml profile configurations for release builds.",
                "source": "Mock Cargo Optimization",
                "standard_category": "Cargo Profile Standards",
                "enforcement_level": "Recommended",
                "configuration": '[profile.release]\nlto = true\ncodegen-units = 1\npanic = "abort"'
            }
        ]
    }

    standards = mock_standards.get(standard_type, [
        {
            "title": f"Rust {standard_type.title()} Standard",
            "description": f"General {standard_type} standards for Rust development.",
            "source": "Mock Rust Standards",
            "standard_category": "General Standard",
            "enforcement_level": "Informational"
        }
    ])

    return {
        "success": True,
        "standard_type": standard_type,
        "domain": domain,
        "standards": standards,
        "recommendations": _generate_standards_recommendations(standards, standard_type, domain)
    }