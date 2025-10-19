#!/usr/bin/env python3
"""
File Creator MCP Server
=======================

MCP server for complex file operations with pattern learning capabilities.

Architecture:
    Claude Code → MCP Protocol → File Creator → Filesystem + Templates
"""

import asyncio
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

from mcp.server import FastMCP


# ============================================================================
# Create FastMCP server instance
# ============================================================================

mcp = FastMCP(
    name="file-creator",
    instructions="File Creator MCP Server - Complex file operations with template support"
)


# ============================================================================
# MCP Tool Implementations (MVP: 3 critical tools)
# ============================================================================

@mcp.tool()
async def create_single_file(
    file_path: str,
    content: str,
    template_name: Optional[str] = None
) -> str:
    """
    Create a single file with optional template application.

    Args:
        file_path: Absolute path to file
        content: File contents
        template_name: Optional template to apply (e.g., "python_module_template")

    Returns:
        JSON string with result: {"success": bool, "file_path": str, "message": str}
    """
    try:
        path = Path(file_path)

        # Create parent directories if they don't exist
        path.parent.mkdir(parents=True, exist_ok=True)

        # Write file
        path.write_text(content, encoding='utf-8')

        result = {
            "success": True,
            "file_path": str(path.absolute()),
            "message": f"File created successfully: {path.name}",
            "template_applied": template_name if template_name else None
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "file_path": file_path,
            "error": str(e),
            "message": f"Failed to create file: {e}"
        }
        return json.dumps(result, indent=2)


@mcp.tool()
async def create_directory_structure(
    base_path: str,
    structure: dict
) -> str:
    """
    Create a nested directory structure with multiple files and folders.

    Args:
        base_path: Root directory for structure
        structure: Nested dict describing directories and files
            Example: {
                "dir1": {
                    "__init__.py": "",
                    "module.py": "# Module content"
                },
                "dir2": {...}
            }

    Returns:
        JSON string with result: {"success": bool, "created_paths": List[str], "message": str}
    """
    created_paths = []

    try:
        base = Path(base_path)
        base.mkdir(parents=True, exist_ok=True)
        created_paths.append(str(base.absolute()))

        def create_structure(current_path: Path, structure_dict: dict):
            """Recursively create directories and files."""
            for name, content in structure_dict.items():
                item_path = current_path / name

                if isinstance(content, dict):
                    # It's a directory
                    item_path.mkdir(parents=True, exist_ok=True)
                    created_paths.append(str(item_path.absolute()))
                    create_structure(item_path, content)
                else:
                    # It's a file
                    item_path.parent.mkdir(parents=True, exist_ok=True)
                    item_path.write_text(str(content), encoding='utf-8')
                    created_paths.append(str(item_path.absolute()))

        create_structure(base, structure)

        result = {
            "success": True,
            "created_paths": created_paths,
            "count": len(created_paths),
            "message": f"Created {len(created_paths)} items successfully"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "created_paths": created_paths,
            "count": len(created_paths),
            "error": str(e),
            "message": f"Failed to create directory structure: {e}"
        }
        return json.dumps(result, indent=2)


@mcp.tool()
async def batch_create_files(file_list: List[Dict[str, Any]]) -> str:
    """
    Create multiple files in a single operation.

    Args:
        file_list: List of file specifications
            Each spec: {"file_path": str, "content": str, "template_name": Optional[str]}

    Returns:
        JSON string with result: {"success": bool, "created_count": int, "failed": List[str], "message": str}
    """
    created = []
    failed = []

    try:
        for spec in file_list:
            file_path = spec.get("file_path")
            content = spec.get("content", "")
            template_name = spec.get("template_name")

            if not file_path:
                failed.append({"error": "Missing file_path", "spec": spec})
                continue

            try:
                path = Path(file_path)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding='utf-8')
                created.append(str(path.absolute()))
            except Exception as e:
                failed.append({"file_path": file_path, "error": str(e)})

        result = {
            "success": len(failed) == 0,
            "created_count": len(created),
            "failed_count": len(failed),
            "created": created,
            "failed": failed,
            "message": f"Created {len(created)} files, {len(failed)} failed"
        }

        return json.dumps(result, indent=2)

    except Exception as e:
        result = {
            "success": False,
            "created_count": len(created),
            "failed_count": len(failed),
            "created": created,
            "failed": failed,
            "error": str(e),
            "message": f"Batch operation failed: {e}"
        }
        return json.dumps(result, indent=2)


# ============================================================================
# Placeholder implementations for remaining tools (Tier 2)
# ============================================================================

@mcp.tool()
async def apply_file_template(
    template_name: str,
    variables: dict,
    output_path: str
) -> str:
    """
    Apply a template with variable substitution and write to file.

    Args:
        template_name: Template identifier
        variables: Template variables for substitution
        output_path: Where to write the rendered template

    Returns:
        JSON string with result
    """
    result = {
        "success": False,
        "message": "Template system not yet implemented (Tier 2)",
        "template_name": template_name,
        "output_path": output_path
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def search_file_templates(
    query: str,
    language: Optional[str] = None
) -> str:
    """
    Search available file templates by keywords or language.

    Args:
        query: Search query
        language: Optional language filter

    Returns:
        JSON string with template list
    """
    result = {
        "success": False,
        "message": "Template search not yet implemented (Tier 2)",
        "query": query,
        "templates": []
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def get_template_info(template_name: str) -> str:
    """
    Get detailed information about a specific template.

    Args:
        template_name: Template identifier

    Returns:
        JSON string with template metadata
    """
    result = {
        "success": False,
        "message": "Template info not yet implemented (Tier 2)",
        "template_name": template_name
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def query_synapse_templates(query: str) -> str:
    """
    Query No3sis-specific templates.

    Args:
        query: No3sis-specific query

    Returns:
        JSON string with No3sis templates
    """
    result = {
        "success": False,
        "message": "No3sis template integration not yet implemented (Tier 2)",
        "query": query,
        "templates": []
    }
    return json.dumps(result, indent=2)


# ============================================================================
# Main entry point
# ============================================================================

async def main():
    """Main entry point: runs MCP server via stdio."""
    await mcp.run_stdio_async()


if __name__ == "__main__":
    asyncio.run(main())
