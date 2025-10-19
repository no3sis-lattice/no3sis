"""
File Creator Synapse Integration Tools

Connects file-creator to the Synapse knowledge graph for:
- Template discovery and retrieval
- File structure pattern search
- Best practices from knowledge base
"""

import sys
import asyncio
from pathlib import Path
from typing import Dict, Any, List, Optional

# Import Synapse search functionality
sys.path.append(str(Path.home() / ".no3sis-system" / ".no3sis" / "neo4j"))

try:
    from no3sis_search import search_synapse_context
    from no3sis_template import get_template_content
    SYNAPSE_AVAILABLE = True
except ImportError:
    SYNAPSE_AVAILABLE = False
    print("⚠️  Synapse components not available, using mock implementations")


async def query_synapse_templates(template_name: str) -> Dict[str, Any]:
    """
    Search for templates in the Synapse knowledge graph.

    Args:
        template_name: Name of template to find

    Returns:
        Dict with template content and metadata
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_template_search(template_name)

    try:
        # Search for the specific template
        query = f"template {template_name} file creation boilerplate"

        results = search_synapse_context(
            query=query,
            max_results=5,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "template_content": None
            }

        # Try to extract template content from results
        template_content = _extract_template_from_results(results, template_name)

        if template_content:
            return {
                "success": True,
                "template_name": template_name,
                "template_content": template_content,
                "source": "synapse_graph"
            }

        # Try direct template retrieval if available
        try:
            direct_content = get_template_content(template_name)
            if direct_content:
                return {
                    "success": True,
                    "template_name": template_name,
                    "template_content": direct_content,
                    "source": "synapse_direct"
                }
        except:
            pass

        return {
            "success": False,
            "error": f"Template {template_name} not found in knowledge graph",
            "template_content": None
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying Synapse for template: {e}",
            "template_content": None
        }


async def search_file_patterns(pattern_query: str) -> Dict[str, Any]:
    """
    Search for file structure patterns in the knowledge graph.

    Args:
        pattern_query: Search query for file patterns

    Returns:
        Dict with matching patterns and recommendations
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_pattern_search(pattern_query)

    try:
        query = f"file structure pattern {pattern_query} directory organization"

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

        patterns = _extract_patterns_from_results(results)

        return {
            "success": True,
            "query": pattern_query,
            "patterns": patterns,
            "recommendations": _generate_pattern_recommendations(patterns)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error searching file patterns: {e}",
            "patterns": []
        }


def _extract_template_from_results(results: Dict, template_name: str) -> Optional[str]:
    """Extract template content from Synapse search results."""
    if not results.get("context"):
        return None

    for item in results["context"]:
        content = item.get("content", "")

        # Look for template-like content
        if template_name.lower() in content.lower():
            # Try to extract the actual template content
            lines = content.split('\n')
            template_lines = []
            in_template = False

            for line in lines:
                if 'template' in line.lower() and template_name.lower() in line.lower():
                    in_template = True
                    continue
                elif in_template and line.strip() == '':
                    if template_lines:  # End of template
                        break
                elif in_template:
                    template_lines.append(line)

            if template_lines:
                return '\n'.join(template_lines)

    return None


def _extract_patterns_from_results(results: Dict) -> List[Dict[str, Any]]:
    """Extract file patterns from search results."""
    patterns = []

    if not results.get("context"):
        return patterns

    for item in results["context"]:
        content = item.get("content", "")

        # Look for directory structures
        if any(indicator in content.lower() for indicator in ["├──", "└──", "directory", "folder"]):
            patterns.append({
                "type": "directory_structure",
                "content": content,
                "source": item.get("source", "unknown"),
                "confidence": 0.8
            })

        # Look for file conventions
        elif any(indicator in content.lower() for indicator in ["naming convention", "file structure", "organization"]):
            patterns.append({
                "type": "file_convention",
                "content": content,
                "source": item.get("source", "unknown"),
                "confidence": 0.7
            })

    return patterns


def _generate_pattern_recommendations(patterns: List[Dict[str, Any]]) -> List[str]:
    """Generate recommendations based on found patterns."""
    recommendations = []

    if not patterns:
        recommendations.append("Consider using standard project structure conventions")
        return recommendations

    # Analyze patterns and generate specific recommendations
    has_directory_structure = any(p["type"] == "directory_structure" for p in patterns)
    has_file_conventions = any(p["type"] == "file_convention" for p in patterns)

    if has_directory_structure:
        recommendations.append("Found directory structure patterns - consider following established conventions")

    if has_file_conventions:
        recommendations.append("Apply consistent file naming conventions based on project standards")

    recommendations.append(f"Based on {len(patterns)} patterns found in knowledge graph")

    return recommendations


def _mock_template_search(template_name: str) -> Dict[str, Any]:
    """Mock template search for development/testing."""
    return {
        "success": False,
        "error": "Synapse not available - using fallback templates",
        "template_content": None
    }


def _mock_pattern_search(pattern_query: str) -> Dict[str, Any]:
    """Mock pattern search for development/testing."""
    return {
        "success": False,
        "error": "Synapse not available - using basic patterns",
        "patterns": []
    }