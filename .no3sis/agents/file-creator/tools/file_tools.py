"""
File Creation Tools

Core functionality for creating files and directories.
"""

import os
import asyncio
from pathlib import Path
from typing import Dict, Any, List, Optional
from datetime import datetime


async def create_file(file_path: str, content: str = "", template_name: Optional[str] = None) -> Dict[str, Any]:
    """
    Create a single file with optional template processing.

    Args:
        file_path: Path where file should be created
        content: Content to write to file
        template_name: Optional template to apply

    Returns:
        Dict with creation status and details
    """
    try:
        path = Path(file_path)

        # Check if file already exists
        if path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"⚠️ File already exists: {file_path}\n→ Action: Skipping file creation"
                }],
                "success": False,
                "reason": "file_exists"
            }

        # Create parent directories if they don't exist
        path.parent.mkdir(parents=True, exist_ok=True)

        # Apply template if specified
        if template_name:
            from .template_tools import apply_template
            template_result = await apply_template(template_name, {"content": content})
            if template_result.get("success"):
                content = template_result.get("processed_content", content)

        # Replace common placeholders
        content = _replace_placeholders(content)

        # Write file
        path.write_text(content, encoding='utf-8')

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Created file: {file_path}"
            }],
            "success": True,
            "file_path": str(path),
            "template_used": template_name
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to create file {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def create_directory(dir_path: str, structure: Optional[Dict] = None) -> Dict[str, Any]:
    """
    Create directory structure.

    Args:
        dir_path: Directory path to create
        structure: Optional nested structure definition

    Returns:
        Dict with creation status and details
    """
    try:
        path = Path(dir_path)

        # Create the main directory
        path.mkdir(parents=True, exist_ok=True)

        results = [f"✓ Created directory: {dir_path}"]

        # Create nested structure if provided
        if structure:
            for item_name, item_config in structure.items():
                item_path = path / item_name

                if isinstance(item_config, dict):
                    # It's a subdirectory
                    subdir_result = await create_directory(str(item_path), item_config)
                    if subdir_result.get("success"):
                        results.extend(subdir_result.get("details", []))
                elif isinstance(item_config, str):
                    # It's a file with content
                    file_result = await create_file(str(item_path), item_config)
                    if file_result.get("success"):
                        results.append(f"✓ Created file: {item_name}")

        return {
            "content": [{
                "type": "text",
                "text": "\n".join(results)
            }],
            "success": True,
            "directory_path": str(path),
            "details": results
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to create directory {dir_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def batch_create(file_list: List[Dict]) -> Dict[str, Any]:
    """
    Create multiple files in batch operation.

    Args:
        file_list: List of file definitions with path, content, template

    Returns:
        Dict with batch creation status and details
    """
    results = []
    success_count = 0
    failure_count = 0

    for file_def in file_list:
        file_path = file_def.get("path", "")
        content = file_def.get("content", "")
        template = file_def.get("template")

        if not file_path:
            results.append(f"❌ Skipped file: missing path")
            failure_count += 1
            continue

        result = await create_file(file_path, content, template)

        if result.get("success"):
            results.append(f"✓ Created file: {file_path}")
            success_count += 1
        else:
            results.append(f"❌ Failed file: {file_path} - {result.get('reason', 'unknown')}")
            failure_count += 1

    return {
        "content": [{
            "type": "text",
            "text": f"Batch creation completed:\n" +
                   f"✓ Success: {success_count}\n" +
                   f"❌ Failed: {failure_count}\n\n" +
                   "\n".join(results)
        }],
        "success": failure_count == 0,
        "success_count": success_count,
        "failure_count": failure_count,
        "details": results
    }


def _replace_placeholders(content: str) -> str:
    """Replace common placeholders in content."""
    current_date = datetime.now().strftime("%Y-%m-%d")

    replacements = {
        "[CURRENT_DATE]": current_date,
        "[DATE]": current_date,
        "[YYYY-MM-DD]": current_date,
        "[PROJECT_ROOT]": os.getcwd()
    }

    for placeholder, value in replacements.items():
        content = content.replace(placeholder, value)

    return content