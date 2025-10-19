"""
Template Management Tools

Tools for working with templates and applying them to content.
"""

import re
import asyncio
from pathlib import Path
from typing import Dict, Any, List, Optional


async def apply_template(template_name: str, variables: Dict[str, str]) -> Dict[str, Any]:
    """
    Apply a template with variable substitution.

    Args:
        template_name: Name of template to apply
        variables: Dictionary of variables to substitute

    Returns:
        Dict with processed content and status
    """
    try:
        # First try to get template from Synapse
        from .no3sis_integration import query_synapse_templates

        template_result = await query_synapse_templates(template_name)

        if template_result.get("success") and template_result.get("template_content"):
            template_content = template_result["template_content"]
        else:
            # Fallback to local templates or generate basic template
            template_content = _get_fallback_template(template_name)

        # Process template with variables
        processed_content = _process_template_variables(template_content, variables)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Applied template: {template_name}"
            }],
            "success": True,
            "template_name": template_name,
            "processed_content": processed_content,
            "variables_used": list(variables.keys())
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to apply template {template_name}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def get_template(template_name: str) -> Dict[str, Any]:
    """
    Retrieve a template by name.

    Args:
        template_name: Name of template to retrieve

    Returns:
        Dict with template content and metadata
    """
    try:
        # Try Synapse first
        from .no3sis_integration import query_synapse_templates

        result = await query_synapse_templates(template_name)

        if result.get("success"):
            return {
                "content": [{
                    "type": "text",
                    "text": f"✓ Retrieved template: {template_name}"
                }],
                "success": True,
                "template_name": template_name,
                "template_content": result.get("template_content", ""),
                "source": "synapse"
            }

        # Fallback to local
        template_content = _get_fallback_template(template_name)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Retrieved fallback template: {template_name}"
            }],
            "success": True,
            "template_name": template_name,
            "template_content": template_content,
            "source": "fallback"
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to retrieve template {template_name}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def list_templates() -> Dict[str, Any]:
    """
    List available templates.

    Returns:
        Dict with template list and metadata
    """
    try:
        # Get templates from Synapse
        from .no3sis_integration import search_file_patterns

        synapse_templates = await search_file_patterns("templates")

        fallback_templates = [
            "spec.md.template",
            "readme.md.template",
            "technical-spec.md.template",
            "tasks.md.template",
            "python-module.py.template",
            "typescript-component.tsx.template"
        ]

        available_templates = []

        if synapse_templates.get("success"):
            available_templates.extend(synapse_templates.get("templates", []))

        available_templates.extend(fallback_templates)

        return {
            "content": [{
                "type": "text",
                "text": f"Available templates ({len(available_templates)}):\n" +
                       "\n".join(f"- {tmpl}" for tmpl in available_templates)
            }],
            "success": True,
            "templates": available_templates,
            "count": len(available_templates)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to list templates: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


def _process_template_variables(template_content: str, variables: Dict[str, str]) -> str:
    """Process template variable substitutions."""
    processed = template_content

    # Replace [VARIABLE] style placeholders
    for var_name, var_value in variables.items():
        patterns = [
            f"[{var_name.upper()}]",
            f"[{var_name.lower()}]",
            f"[{var_name}]",
            f"{{{var_name}}}",
            f"{{{{ {var_name} }}}}"
        ]

        for pattern in patterns:
            processed = processed.replace(pattern, var_value)

    return processed


def _get_fallback_template(template_name: str) -> str:
    """Get basic fallback templates when Synapse is unavailable."""

    templates = {
        "spec.md.template": """# [SPEC_NAME]

## Overview
[OVERVIEW]

## Requirements
[REQUIREMENTS]

## Implementation
[IMPLEMENTATION]

---
Created: [CURRENT_DATE]
""",
        "readme.md.template": """# [PROJECT_NAME]

[DESCRIPTION]

## Installation
```bash
[INSTALL_COMMANDS]
```

## Usage
[USAGE]

## License
[LICENSE]
""",
        "technical-spec.md.template": """# Technical Specification: [SPEC_NAME]

## Architecture
[ARCHITECTURE]

## Components
[COMPONENTS]

## Data Flow
[DATA_FLOW]

## API Design
[API_DESIGN]
""",
        "tasks.md.template": """# Tasks: [PROJECT_NAME]

## Current Sprint
[CURRENT_TASKS]

## Backlog
[BACKLOG_TASKS]

## Completed
[COMPLETED_TASKS]
""",
        "python-module.py.template": '''"""
[MODULE_DESCRIPTION]
"""

[IMPORTS]


class [CLASS_NAME]:
    """[CLASS_DESCRIPTION]"""

    def __init__(self):
        pass

    def [METHOD_NAME](self):
        """[METHOD_DESCRIPTION]"""
        pass
''',
        "typescript-component.tsx.template": '''import React from 'react';

interface [COMPONENT_NAME]Props {
  [PROPS]
}

export const [COMPONENT_NAME]: React.FC<[COMPONENT_NAME]Props> = ({
  [PROP_DESTRUCTURE]
}) => {
  return (
    <div>
      [COMPONENT_CONTENT]
    </div>
  );
};

export default [COMPONENT_NAME];
'''
    }

    return templates.get(template_name, f"# {template_name}\n\n[CONTENT]\n")