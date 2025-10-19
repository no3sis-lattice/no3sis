"""
Tool Runner Synapse Integration

Connects tool-runner to the Synapse knowledge graph for:
- Tool mapping and discovery
- Command history and patterns
- Best practices from knowledge base
"""

import sys
import json
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


async def query_tool_mapping(tool_name: str) -> Dict[str, Any]:
    """
    Query Synapse for tool mapping information.

    Args:
        tool_name: Name of tool to look up

    Returns:
        Dict with tool mapping and execution info
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_tool_mapping(tool_name)

    try:
        # Search for tool mapping in knowledge graph
        query = f"tool mapping {tool_name} script execution command"

        results = search_synapse_context(
            query=query,
            max_results=5,
            auto_activate=True
        )

        if "error" in results:
            return {
                "success": False,
                "error": results["error"],
                "tool_mapping": None
            }

        # Extract tool mapping from results
        tool_mapping = _extract_tool_mapping_from_results(results, tool_name)

        if tool_mapping:
            return {
                "success": True,
                "tool_name": tool_name,
                "tool_mapping": tool_mapping,
                "source": "synapse_graph"
            }

        # Try to find in local tool-mapping.json
        mapping_file = Path.cwd() / "tool-mapping.json"
        if mapping_file.exists():
            local_mapping = _load_local_tool_mapping(mapping_file, tool_name)
            if local_mapping:
                return {
                    "success": True,
                    "tool_name": tool_name,
                    "tool_mapping": local_mapping,
                    "source": "local_file"
                }

        return {
            "success": False,
            "error": f"Tool mapping for {tool_name} not found",
            "tool_mapping": None
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error querying tool mapping: {e}",
            "tool_mapping": None
        }


async def execute_synapse_tool(tool_name: str, args: List[str] = None) -> Dict[str, Any]:
    """
    Execute a Synapse-defined tool.

    Args:
        tool_name: Name of tool to execute
        args: Arguments to pass to tool

    Returns:
        Dict with execution results
    """
    try:
        # Get tool mapping
        mapping_result = await query_tool_mapping(tool_name)

        if not mapping_result.get("success"):
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Tool mapping not found for: {tool_name}"
                }],
                "success": False,
                "error": mapping_result.get("error", "Unknown error")
            }

        tool_mapping = mapping_result["tool_mapping"]

        # Build command to execute
        script_path = tool_mapping.get("script", "")
        expected_args = tool_mapping.get("args", [])

        if not script_path:
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ No script path defined for tool: {tool_name}"
                }],
                "success": False,
                "error": "missing_script_path"
            }

        # Resolve script path (relative to synapse root)
        if not Path(script_path).is_absolute():
            synapse_root = Path.home() / ".no3sis-system"
            script_path = synapse_root / script_path

        if not Path(script_path).exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Script not found: {script_path}"
                }],
                "success": False,
                "error": "script_not_found"
            }

        # Execute the tool using execution_tools
        from .execution_tools import execute_script

        result = await execute_script(str(script_path), args or [])

        # Enhance result with tool information
        if result.get("success"):
            result["tool_name"] = tool_name
            result["tool_mapping"] = tool_mapping

        return result

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Error executing Synapse tool {tool_name}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


def _extract_tool_mapping_from_results(results: Dict, tool_name: str) -> Optional[Dict]:
    """Extract tool mapping information from search results."""
    if not results.get("context"):
        return None

    for item in results["context"]:
        content = item.get("content", "")

        # Look for JSON-like tool mapping
        try:
            # Try to find JSON in the content
            import re
            json_match = re.search(r'\{[^{}]*"' + re.escape(tool_name) + r'"[^{}]*\}', content)
            if json_match:
                json_str = json_match.group(0)
                mapping_data = json.loads(json_str)
                if tool_name in mapping_data:
                    return mapping_data[tool_name]

            # Look for structured mapping info
            lines = content.split('\n')
            in_mapping = False
            mapping_info = {}

            for line in lines:
                if tool_name.lower() in line.lower() and ('script' in line.lower() or 'command' in line.lower()):
                    in_mapping = True
                    continue
                elif in_mapping:
                    if 'script:' in line.lower():
                        mapping_info['script'] = line.split(':', 1)[1].strip().strip('"')
                    elif 'args:' in line.lower():
                        args_str = line.split(':', 1)[1].strip()
                        if args_str.startswith('[') and args_str.endswith(']'):
                            mapping_info['args'] = json.loads(args_str)
                    elif line.strip() == '' or line.startswith('  '):
                        continue
                    else:
                        break

            if mapping_info.get('script'):
                return mapping_info

        except (json.JSONDecodeError, ValueError):
            continue

    return None


def _load_local_tool_mapping(mapping_file: Path, tool_name: str) -> Optional[Dict]:
    """Load tool mapping from local file."""
    try:
        with open(mapping_file, 'r') as f:
            mappings = json.load(f)
            return mappings.get(tool_name)
    except (json.JSONDecodeError, FileNotFoundError):
        return None


def _mock_tool_mapping(tool_name: str) -> Dict[str, Any]:
    """Mock tool mapping for development/testing."""
    # Provide mock mappings for known Synapse tools
    mock_mappings = {
        "SynapseSearch": {
            "script": ".no3sis/neo4j/synapse_search.py",
            "args": ["query"]
        },
        "SynapseTemplate": {
            "script": ".no3sis/neo4j/synapse_template.py",
            "args": ["template_name"]
        },
        "SynapseStandard": {
            "script": ".no3sis/neo4j/synapse_standard.py",
            "args": ["standard_name", "language"]
        },
        "SynapseHealth": {
            "script": ".no3sis/neo4j/synapse_health.py",
            "args": []
        }
    }

    if tool_name in mock_mappings:
        return {
            "success": True,
            "tool_name": tool_name,
            "tool_mapping": mock_mappings[tool_name],
            "source": "mock"
        }
    else:
        return {
            "success": False,
            "error": f"No mock mapping available for {tool_name}",
            "tool_mapping": None
        }