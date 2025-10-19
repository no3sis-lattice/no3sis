"""
Documentation Writer Synapse Integration

Connects docs-writer to the Synapse knowledge graph for:
- Documentation template discovery
- Style guide retrieval
- Best practice patterns
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


async def query_doc_templates(template_type: str) -> Dict[str, Any]:
    """
    Search for documentation templates in Synapse knowledge graph.

    Args:
        template_type: Type of template (api, readme, user-guide, tutorial)

    Returns:
        Dict with template content and metadata
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_template_query(template_type)

    try:
        query = f"documentation template {template_type} writing guide format"

        results = search_synapse_context(
            query=query,
            max_results=10,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "templates": []
            }

        templates = _extract_templates_from_results(results, template_type)

        return {
            "success": True,
            "template_type": template_type,
            "templates": templates,
            "source": "synapse_graph"
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying doc templates: {e}",
            "templates": []
        }


async def search_style_guides(domain: str = "general") -> Dict[str, Any]:
    """
    Search for style guides and writing standards.

    Args:
        domain: Domain for style guide (api, technical, user, general)

    Returns:
        Dict with style guide information
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_style_guide_search(domain)

    try:
        query = f"style guide writing standards {domain} documentation best practices"

        results = search_synapse_context(
            query=query,
            max_results=8,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "style_guides": []
            }

        style_guides = _extract_style_guides_from_results(results, domain)

        return {
            "success": True,
            "domain": domain,
            "style_guides": style_guides,
            "recommendations": _generate_style_recommendations(style_guides)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error searching style guides: {e}",
            "style_guides": []
        }


def _extract_templates_from_results(results: Dict, template_type: str) -> List[Dict[str, Any]]:
    """Extract templates from Synapse search results."""
    templates = []

    if not results.get("context"):
        return templates

    for item in results["context"]:
        content = item.get("content", "")

        if any(keyword in content.lower() for keyword in [template_type, "template", "documentation"]):
            templates.append({
                "content": content,
                "source": item.get("source", "unknown"),
                "type": template_type,
                "relevance": _calculate_template_relevance(content, template_type)
            })

    # Sort by relevance
    templates.sort(key=lambda x: x["relevance"], reverse=True)
    return templates[:5]  # Return top 5


def _extract_style_guides_from_results(results: Dict, domain: str) -> List[Dict[str, Any]]:
    """Extract style guides from search results."""
    guides = []

    if not results.get("context"):
        return guides

    for item in results["context"]:
        content = item.get("content", "")

        if any(keyword in content.lower() for keyword in ["style", "guide", "standard", "convention"]):
            guides.append({
                "content": content,
                "source": item.get("source", "unknown"),
                "domain": domain,
                "guidelines": _extract_guidelines_from_content(content)
            })

    return guides


def _calculate_template_relevance(content: str, template_type: str) -> float:
    """Calculate relevance score for template."""
    score = 0.0

    # Check for template type keywords
    type_keywords = {
        "api": ["api", "endpoint", "function", "method", "parameter"],
        "readme": ["readme", "overview", "installation", "usage"],
        "user-guide": ["user", "guide", "tutorial", "how-to", "step"],
        "tutorial": ["tutorial", "example", "walkthrough", "learn"]
    }

    keywords = type_keywords.get(template_type, [])
    content_lower = content.lower()

    for keyword in keywords:
        if keyword in content_lower:
            score += 1.0

    # Bonus for structure indicators
    if "##" in content or "###" in content:
        score += 0.5

    # Bonus for code examples
    if "```" in content:
        score += 0.3

    return score


def _extract_guidelines_from_content(content: str) -> List[str]:
    """Extract style guidelines from content."""
    guidelines = []

    # Look for bullet points and numbered lists
    lines = content.split('\n')

    for line in lines:
        stripped = line.strip()

        # Bullet points
        if stripped.startswith(('- ', '* ', '+ ')):
            guidelines.append(stripped[2:].strip())

        # Numbered lists
        elif stripped and stripped[0].isdigit() and '. ' in stripped:
            guidelines.append(stripped.split('. ', 1)[1])

        # Lines that start with common guideline words
        elif any(stripped.lower().startswith(word) for word in ['use', 'avoid', 'ensure', 'always', 'never']):
            guidelines.append(stripped)

    return guidelines[:10]  # Return top 10 guidelines


def _generate_style_recommendations(style_guides: List[Dict]) -> List[str]:
    """Generate recommendations based on style guides."""
    recommendations = []

    if not style_guides:
        recommendations.extend([
            "Use clear, concise language",
            "Structure content with headings",
            "Include practical examples",
            "Maintain consistent formatting"
        ])
        return recommendations

    # Analyze common themes
    all_guidelines = []
    for guide in style_guides:
        all_guidelines.extend(guide.get("guidelines", []))

    # Common recommendation patterns
    common_themes = {
        "clarity": ["clear", "simple", "concise"],
        "structure": ["heading", "section", "organize"],
        "examples": ["example", "sample", "demonstrate"],
        "consistency": ["consistent", "uniform", "standard"]
    }

    for theme, keywords in common_themes.items():
        if any(any(keyword in guideline.lower() for keyword in keywords) for guideline in all_guidelines):
            if theme == "clarity":
                recommendations.append("Prioritize clear, simple language")
            elif theme == "structure":
                recommendations.append("Use proper heading hierarchy")
            elif theme == "examples":
                recommendations.append("Include practical examples")
            elif theme == "consistency":
                recommendations.append("Maintain consistent formatting")

    return recommendations or ["Follow established documentation standards"]


def _mock_template_query(template_type: str) -> Dict[str, Any]:
    """Mock template query for development/testing."""
    mock_templates = {
        "api": [{
            "content": f"# API Documentation Template\n\n## {template_type.title()} Overview\n\n### Endpoints\n\n### Parameters\n\n### Examples",
            "source": "mock",
            "type": template_type,
            "relevance": 1.0
        }],
        "readme": [{
            "content": "# Project Name\n\n## Installation\n\n## Usage\n\n## License",
            "source": "mock",
            "type": template_type,
            "relevance": 1.0
        }]
    }

    return {
        "success": True,
        "template_type": template_type,
        "templates": mock_templates.get(template_type, []),
        "source": "mock"
    }


def _mock_style_guide_search(domain: str) -> Dict[str, Any]:
    """Mock style guide search for development/testing."""
    mock_guides = [{
        "content": f"Style guide for {domain} documentation",
        "source": "mock",
        "domain": domain,
        "guidelines": [
            "Use clear, concise language",
            "Structure content logically",
            "Include examples where helpful"
        ]
    }]

    return {
        "success": True,
        "domain": domain,
        "style_guides": mock_guides,
        "recommendations": ["Follow standard writing practices"]
    }