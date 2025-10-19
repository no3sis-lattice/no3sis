"""
TypeScript Specialist Synapse Integration

Connects typescript-specialist to the Synapse knowledge graph for:
- TypeScript/JavaScript-specific pattern discovery
- Framework best practice retrieval
- Build optimization recommendations
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


async def query_typescript_patterns(pattern_type: str, context: str = "") -> Dict[str, Any]:
    """
    Search for TypeScript patterns in the Synapse knowledge graph.

    Args:
        pattern_type: Type of pattern (react, node, async, testing, performance, etc.)
        context: Additional context for the search

    Returns:
        Dict with TypeScript patterns and recommendations
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_typescript_pattern_search(pattern_type, context)

    try:
        query = f"typescript javascript pattern {pattern_type} {context} best practice idiom framework"

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

        patterns = _extract_typescript_patterns_from_results(results, pattern_type)

        return {
            "success": True,
            "pattern_type": pattern_type,
            "patterns": patterns,
            "recommendations": _generate_typescript_recommendations(patterns, pattern_type)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying TypeScript patterns: {e}",
            "patterns": []
        }


async def search_typescript_standards(standard_type: str, framework: str = "general") -> Dict[str, Any]:
    """
    Search for TypeScript coding standards and conventions.

    Args:
        standard_type: Type of standard (eslint, prettier, tsconfig, testing, etc.)
        framework: Framework context (react, vue, angular, svelte, node)

    Returns:
        Dict with TypeScript standards and guidelines
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_typescript_standards_search(standard_type, framework)

    try:
        query = f"typescript javascript standard {standard_type} {framework} eslint prettier tsconfig convention guideline"

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

        standards = _extract_typescript_standards_from_results(results, standard_type, framework)

        return {
            "success": True,
            "standard_type": standard_type,
            "framework": framework,
            "standards": standards,
            "recommendations": _generate_standards_recommendations(standards, standard_type, framework)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying TypeScript standards: {e}",
            "standards": []
        }


def _extract_typescript_patterns_from_results(results: Dict[str, Any], pattern_type: str) -> List[Dict[str, Any]]:
    """Extract TypeScript patterns from Synapse search results."""
    patterns = []

    context = results.get("context", {})
    primary_matches = context.get("primary_matches", [])

    for match in primary_matches[:8]:  # Limit to top 8 matches
        pattern_entry = {
            "title": match.get("title", "TypeScript Pattern"),
            "description": match.get("snippet", "")[:200] + "..." if len(match.get("snippet", "")) > 200 else match.get("snippet", ""),
            "source": match.get("source", "Unknown"),
            "relevance_score": match.get("score", 0.0),
            "pattern_category": _categorize_pattern(match.get("content", ""), pattern_type)
        }

        # Extract code examples if available
        content = match.get("content", "")
        code_examples = _extract_code_examples(content)
        if code_examples:
            pattern_entry["examples"] = code_examples[:2]  # Limit to 2 examples

        patterns.append(pattern_entry)

    return patterns


def _extract_typescript_standards_from_results(results: Dict[str, Any], standard_type: str, framework: str) -> List[Dict[str, Any]]:
    """Extract TypeScript standards from Synapse search results."""
    standards = []

    context = results.get("context", {})
    primary_matches = context.get("primary_matches", [])

    for match in primary_matches[:6]:  # Limit to top 6 matches
        standard_entry = {
            "title": match.get("title", "TypeScript Standard"),
            "description": match.get("snippet", "")[:150] + "..." if len(match.get("snippet", "")) > 150 else match.get("snippet", ""),
            "source": match.get("source", "Unknown"),
            "standard_category": _categorize_standard(match.get("content", ""), standard_type),
            "framework_specific": framework != "general"
        }

        # Extract configuration examples
        content = match.get("content", "")
        config_examples = _extract_config_examples(content, standard_type)
        if config_examples:
            standard_entry["configuration"] = config_examples

        standards.append(standard_entry)

    return standards


def _categorize_pattern(content: str, pattern_type: str) -> str:
    """Categorize the pattern based on content analysis."""
    content_lower = content.lower()

    # Framework-specific categorization
    if pattern_type == "react":
        if "hook" in content_lower or "useeffect" in content_lower or "usestate" in content_lower:
            return "React Hooks"
        elif "component" in content_lower:
            return "React Components"
        elif "context" in content_lower:
            return "React Context"
        else:
            return "React General"

    elif pattern_type == "node":
        if "express" in content_lower or "api" in content_lower:
            return "Node.js API"
        elif "middleware" in content_lower:
            return "Node.js Middleware"
        elif "database" in content_lower or "mongodb" in content_lower or "postgres" in content_lower:
            return "Node.js Database"
        else:
            return "Node.js General"

    elif pattern_type == "async":
        if "promise" in content_lower:
            return "Promise Patterns"
        elif "async" in content_lower and "await" in content_lower:
            return "Async/Await Patterns"
        elif "callback" in content_lower:
            return "Callback Patterns"
        else:
            return "Async General"

    elif pattern_type == "testing":
        if "jest" in content_lower or "vitest" in content_lower:
            return "Unit Testing"
        elif "cypress" in content_lower or "playwright" in content_lower:
            return "E2E Testing"
        elif "mock" in content_lower:
            return "Testing Mocks"
        else:
            return "Testing General"

    elif pattern_type == "performance":
        if "bundle" in content_lower or "webpack" in content_lower or "vite" in content_lower:
            return "Build Performance"
        elif "memory" in content_lower or "leak" in content_lower:
            return "Memory Optimization"
        elif "lazy" in content_lower or "dynamic import" in content_lower:
            return "Code Splitting"
        else:
            return "Performance General"

    elif pattern_type == "svelte":
        if "store" in content_lower or "writable" in content_lower or "readable" in content_lower:
            return "Svelte Stores"
        elif "reactive" in content_lower or "$:" in content:
            return "Svelte Reactivity"
        elif "component" in content_lower:
            return "Svelte Components"
        else:
            return "Svelte General"

    return "General Pattern"


def _categorize_standard(content: str, standard_type: str) -> str:
    """Categorize the standard based on content analysis."""
    content_lower = content.lower()

    if standard_type == "eslint":
        if "typescript" in content_lower:
            return "ESLint TypeScript Rules"
        elif "react" in content_lower:
            return "ESLint React Rules"
        else:
            return "ESLint General Rules"

    elif standard_type == "prettier":
        return "Code Formatting"

    elif standard_type == "tsconfig":
        if "strict" in content_lower:
            return "TypeScript Strict Configuration"
        elif "compiler" in content_lower:
            return "TypeScript Compiler Options"
        else:
            return "TypeScript Configuration"

    elif standard_type == "testing":
        if "jest" in content_lower:
            return "Jest Configuration"
        elif "cypress" in content_lower:
            return "Cypress Configuration"
        else:
            return "Testing Configuration"

    return "General Standard"


def _extract_code_examples(content: str) -> List[str]:
    """Extract code examples from content."""
    import re

    # Look for code blocks (markdown or other formats)
    code_patterns = [
        r'```(?:typescript|ts|javascript|js)?\n(.*?)\n```',
        r'`([^`]{20,})`',  # Inline code longer than 20 chars
        r'^\s{4,}([^\n]{20,})$'  # Indented code blocks
    ]

    examples = []
    for pattern in code_patterns:
        matches = re.findall(pattern, content, re.MULTILINE | re.DOTALL)
        for match in matches:
            code = match.strip()
            if len(code) > 20 and any(keyword in code for keyword in ['function', 'const', 'interface', 'type', 'class']):
                examples.append(code[:200] + "..." if len(code) > 200 else code)

    return examples[:3]  # Return up to 3 examples


def _extract_config_examples(content: str, standard_type: str) -> Optional[str]:
    """Extract configuration examples based on standard type."""
    import re

    if standard_type == "eslint":
        # Look for ESLint config
        eslint_pattern = r'(?:eslintrc|\.eslintrc).*?\{(.*?)\}'
        matches = re.findall(eslint_pattern, content, re.DOTALL | re.IGNORECASE)
        if matches:
            return matches[0][:300]

    elif standard_type == "prettier":
        # Look for Prettier config
        prettier_pattern = r'(?:prettierrc|\.prettierrc).*?\{(.*?)\}'
        matches = re.findall(prettier_pattern, content, re.DOTALL | re.IGNORECASE)
        if matches:
            return matches[0][:300]

    elif standard_type == "tsconfig":
        # Look for tsconfig.json
        tsconfig_pattern = r'(?:tsconfig\.json).*?\{(.*?)\}'
        matches = re.findall(tsconfig_pattern, content, re.DOTALL | re.IGNORECASE)
        if matches:
            return matches[0][:400]

    return None


def _generate_typescript_recommendations(patterns: List[Dict], pattern_type: str) -> List[Dict[str, Any]]:
    """Generate recommendations based on discovered patterns."""
    recommendations = []

    if not patterns:
        return [{
            "type": "no_patterns",
            "message": f"No specific {pattern_type} patterns found in knowledge base",
            "suggestion": "Consider checking TypeScript documentation or community resources"
        }]

    # Group patterns by category
    categories = {}
    for pattern in patterns:
        category = pattern.get("pattern_category", "General")
        if category not in categories:
            categories[category] = []
        categories[category].append(pattern)

    # Generate category-based recommendations
    for category, category_patterns in categories.items():
        if len(category_patterns) >= 2:  # Multiple patterns in same category
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
            "suggestion": "Prioritize implementing these well-matched patterns",
            "patterns": [p["title"] for p in high_relevance[:3]]
        })

    return recommendations


def _generate_standards_recommendations(standards: List[Dict], standard_type: str, framework: str) -> List[Dict[str, Any]]:
    """Generate recommendations based on discovered standards."""
    recommendations = []

    if not standards:
        return [{
            "type": "no_standards",
            "message": f"No specific {standard_type} standards found for {framework}",
            "suggestion": "Consider using general TypeScript standards or community best practices"
        }]

    # Framework-specific standards
    framework_specific = [s for s in standards if s.get("framework_specific", False)]
    if framework_specific:
        recommendations.append({
            "type": "framework_specific",
            "message": f"{len(framework_specific)} {framework}-specific standards found",
            "suggestion": f"Apply these {framework} optimizations for better integration",
            "standards": [s["title"] for s in framework_specific[:2]]
        })

    # Configuration examples available
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

def _mock_typescript_pattern_search(pattern_type: str, context: str) -> Dict[str, Any]:
    """Mock TypeScript pattern search for development."""

    mock_patterns = {
        "react": [
            {
                "title": "React Functional Components with TypeScript",
                "description": "Best practices for typing React functional components with proper prop interfaces and return types.",
                "source": "Mock TypeScript Guide",
                "relevance_score": 0.9,
                "pattern_category": "React Components",
                "examples": [
                    "interface Props { name: string; age?: number; }\nconst Component: React.FC<Props> = ({ name, age = 0 }) => { ... }"
                ]
            },
            {
                "title": "Custom Hooks with TypeScript",
                "description": "Patterns for creating type-safe custom React hooks with proper return type inference.",
                "source": "Mock React Patterns",
                "relevance_score": 0.85,
                "pattern_category": "React Hooks",
                "examples": [
                    "function useCounter(initial: number = 0): [number, () => void] { ... }"
                ]
            }
        ],
        "async": [
            {
                "title": "TypeScript Async/Await Error Handling",
                "description": "Robust error handling patterns for async/await in TypeScript applications.",
                "source": "Mock Async Guide",
                "relevance_score": 0.88,
                "pattern_category": "Async/Await Patterns",
                "examples": [
                    "async function fetchUser(id: string): Promise<User | null> { try { ... } catch { return null; } }"
                ]
            }
        ],
        "svelte": [
            {
                "title": "Svelte Stores with TypeScript",
                "description": "Type-safe Svelte store patterns for state management.",
                "source": "Mock Svelte Guide",
                "relevance_score": 0.87,
                "pattern_category": "Svelte Stores",
                "examples": [
                    "const count = writable<number>(0);\n$: doubled = $count * 2;"
                ]
            }
        ]
    }

    patterns = mock_patterns.get(pattern_type, [
        {
            "title": f"TypeScript {pattern_type.title()} Pattern",
            "description": f"General TypeScript patterns for {pattern_type} development.",
            "source": "Mock TypeScript Patterns",
            "relevance_score": 0.7,
            "pattern_category": "General Pattern"
        }
    ])

    return {
        "success": True,
        "pattern_type": pattern_type,
        "patterns": patterns,
        "recommendations": _generate_typescript_recommendations(patterns, pattern_type)
    }


def _mock_typescript_standards_search(standard_type: str, framework: str) -> Dict[str, Any]:
    """Mock TypeScript standards search for development."""

    mock_standards = {
        "eslint": [
            {
                "title": "TypeScript ESLint Configuration",
                "description": "Recommended ESLint rules for TypeScript projects with strict type checking.",
                "source": "Mock ESLint Guide",
                "standard_category": "ESLint TypeScript Rules",
                "framework_specific": framework != "general",
                "configuration": '"@typescript-eslint/no-unused-vars": "error", "@typescript-eslint/explicit-function-return-type": "warn"'
            }
        ],
        "tsconfig": [
            {
                "title": "Strict TypeScript Configuration",
                "description": "Recommended tsconfig.json settings for maximum type safety.",
                "source": "Mock TypeScript Config",
                "standard_category": "TypeScript Strict Configuration",
                "configuration": '"strict": true, "noUncheckedIndexedAccess": true, "exactOptionalPropertyTypes": true'
            }
        ]
    }

    standards = mock_standards.get(standard_type, [
        {
            "title": f"TypeScript {standard_type.title()} Standard",
            "description": f"General {standard_type} standards for TypeScript development.",
            "source": "Mock TypeScript Standards",
            "standard_category": "General Standard"
        }
    ])

    return {
        "success": True,
        "standard_type": standard_type,
        "framework": framework,
        "standards": standards,
        "recommendations": _generate_standards_recommendations(standards, standard_type, framework)
    }