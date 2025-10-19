#!/usr/bin/env python3
"""
Synapse Template Retrieval Tool
===============================

Retrieves project templates and boilerplate from the Synapse template system.
Used by agents to access standardized project templates and document structures.
"""

import sys
import json
import re
from pathlib import Path
from typing import Dict, Any, Optional, List
from datetime import datetime


def get_template(template_name: str, variables: Optional[Dict[str, str]] = None) -> Dict[str, Any]:
    """
    Retrieve and optionally process a template.

    Args:
        template_name: Name of the template (without .template extension)
        variables: Optional dictionary of variables to substitute in template

    Returns:
        Dictionary containing the template content and metadata
    """
    no3sis_root = Path.home() / ".no3sis-system"
    templates_dir = no3sis_root / ".no3sis" / "templates"

    # Check if templates directory exists
    if not templates_dir.exists():
        return {
            "error": "Templates directory not found",
            "expected_path": str(templates_dir),
            "suggestion": "Verify no3sis installation and template directory"
        }

    # Find the template file (try with and without .template extension)
    template_extensions = [f"{template_name}.template", f"{template_name}.md.template", template_name]
    template_file = None

    for ext in template_extensions:
        candidate = templates_dir / ext
        if candidate.exists():
            template_file = candidate
            break

    if not template_file:
        return {
            "error": f"Template '{template_name}' not found",
            "available_templates": list_available_templates(),
            "searched_paths": [str(templates_dir / ext) for ext in template_extensions],
            "suggestion": "Check available templates or verify template name"
        }

    try:
        content = template_file.read_text(encoding='utf-8')

        # Process template variables if provided
        if variables:
            content = process_template_variables(content, variables)

        return {
            "template_name": template_name,
            "content": content,
            "file_path": str(template_file),
            "size": len(content),
            "variables_processed": bool(variables),
            "detected_variables": extract_template_variables(template_file.read_text(encoding='utf-8')),
            "usage_guidance": generate_usage_guidance(template_name)
        }

    except Exception as e:
        return {
            "error": f"Failed to read template file: {str(e)}",
            "file_path": str(template_file)
        }


def list_available_templates() -> List[str]:
    """List all available templates."""
    no3sis_root = Path.home() / ".no3sis-system"
    templates_dir = no3sis_root / ".no3sis" / "templates"

    if not templates_dir.exists():
        return []

    templates = []
    for template_file in templates_dir.glob("*.template"):
        # Remove .template extension for cleaner naming
        template_name = template_file.name.replace(".template", "")
        templates.append(template_name)

    return sorted(templates)


def extract_template_variables(content: str) -> List[str]:
    """Extract variable placeholders from template content."""
    # Find all [VARIABLE_NAME] patterns
    pattern = r'\[([A-Z_]+)\]'
    variables = re.findall(pattern, content)
    return sorted(list(set(variables)))


def process_template_variables(content: str, variables: Dict[str, str]) -> str:
    """Process template by substituting variables."""
    processed_content = content

    # Add default variables
    default_vars = {
        "CURRENT_DATE": datetime.now().strftime("%Y-%m-%d"),
        "CURRENT_TIMESTAMP": datetime.now().isoformat(),
        "CURRENT_YEAR": str(datetime.now().year)
    }

    # Merge with provided variables (user variables take precedence)
    all_variables = {**default_vars, **variables}

    # Substitute variables
    for var_name, var_value in all_variables.items():
        placeholder = f"[{var_name}]"
        processed_content = processed_content.replace(placeholder, var_value)

    return processed_content


def generate_usage_guidance(template_name: str) -> Dict[str, str]:
    """Generate contextual usage guidance for the template."""
    guidance = {
        "purpose": f"Use the {template_name} template for consistent document structure",
        "customization": "Replace placeholder variables with project-specific content",
        "integration": "Copy and modify template content for your project needs"
    }

    # Add specific guidance based on template type
    if "mission" in template_name:
        guidance["when_to_use"] = "Use for defining product vision and goals"
        guidance["key_sections"] = "Focus on pitch, users, problems, and differentiators"
    elif "spec" in template_name:
        guidance["when_to_use"] = "Use for technical specifications and requirements"
        guidance["key_sections"] = "Define features, architecture, and implementation details"
    elif "api" in template_name:
        guidance["when_to_use"] = "Use for API documentation and endpoint specifications"
        guidance["key_sections"] = "Document endpoints, parameters, and response formats"
    elif "roadmap" in template_name:
        guidance["when_to_use"] = "Use for project planning and milestone tracking"
        guidance["key_sections"] = "Define phases, deliverables, and timelines"

    return guidance


def main():
    """Command-line interface for the no3sis template tool."""
    if len(sys.argv) < 2:
        print(json.dumps({
            "error": "Usage: no3sis_template.py <template_name> [variables_json]",
            "example": "no3sis_template.py mission '{\"PROJECT_NAME\": \"MyApp\", \"PITCH_CONTENT\": \"Revolutionary tool\"}'",
            "available_templates": list_available_templates()
        }, indent=2))
        sys.exit(1)

    template_name = sys.argv[1]
    variables = None

    # Parse variables if provided
    if len(sys.argv) > 2:
        try:
            variables = json.loads(sys.argv[2])
        except json.JSONDecodeError as e:
            print(json.dumps({
                "error": f"Invalid JSON for variables: {str(e)}",
                "example": '{"PROJECT_NAME": "MyApp", "PITCH_CONTENT": "Revolutionary tool"}'
            }, indent=2))
            sys.exit(1)

    result = get_template(template_name, variables)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()