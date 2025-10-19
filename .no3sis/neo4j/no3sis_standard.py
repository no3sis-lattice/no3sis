#!/usr/bin/env python3
"""
Synapse Standard Retrieval Tool
===============================

Retrieves language-specific coding standards from the Synapse language directories.
Used by agents to access consistent coding standards and best practices.
"""

import sys
import json
from pathlib import Path
from typing import Dict, Any, Optional


def get_standard(standard_name: str, language: str) -> Dict[str, Any]:
    """
    Retrieve a specific coding standard for a given language.

    Args:
        standard_name: Name of the standard (e.g., "naming-conventions", "testing-strategy")
        language: Programming language (e.g., "rust", "golang", "typescript")

    Returns:
        Dictionary containing the standard content and metadata
    """
    no3sis_root = Path.home() / ".no3sis-system"
    standards_dir = no3sis_root / ".no3sis" / "languages" / language / "standards"

    # Check if language directory exists
    if not standards_dir.exists():
        return {
            "error": f"No standards found for language: {language}",
            "available_languages": list_available_languages(),
            "suggestion": "Check available languages or verify language name"
        }

    # Find the standard file
    standard_file = standards_dir / f"{standard_name}.md"

    if not standard_file.exists():
        return {
            "error": f"Standard '{standard_name}' not found for {language}",
            "available_standards": list_available_standards(language),
            "suggestion": f"Check available standards for {language}"
        }

    try:
        content = standard_file.read_text(encoding='utf-8')

        return {
            "standard_name": standard_name,
            "language": language,
            "content": content,
            "file_path": str(standard_file),
            "size": len(content),
            "usage_guidance": generate_usage_guidance(standard_name, language)
        }

    except Exception as e:
        return {
            "error": f"Failed to read standard file: {str(e)}",
            "file_path": str(standard_file)
        }


def list_available_languages() -> list:
    """List all available programming languages with standards."""
    no3sis_root = Path.home() / ".no3sis-system"
    languages_dir = no3sis_root / ".no3sis" / "languages"

    if not languages_dir.exists():
        return []

    languages = []
    for lang_dir in languages_dir.iterdir():
        if lang_dir.is_dir() and (lang_dir / "standards").exists():
            languages.append(lang_dir.name)

    return sorted(languages)


def list_available_standards(language: str) -> list:
    """List all available standards for a specific language."""
    no3sis_root = Path.home() / ".no3sis-system"
    standards_dir = no3sis_root / ".no3sis" / "languages" / language / "standards"

    if not standards_dir.exists():
        return []

    standards = []
    for standard_file in standards_dir.glob("*.md"):
        standards.append(standard_file.stem)

    return sorted(standards)


def generate_usage_guidance(standard_name: str, language: str) -> Dict[str, str]:
    """Generate contextual usage guidance for the standard."""
    guidance = {
        "apply_to": f"Use this {standard_name} standard when working on {language} code",
        "enforcement": f"Validate {language} code against these {standard_name} guidelines",
        "integration": f"Reference during {language} code reviews and development"
    }

    # Add specific guidance based on standard type
    if "naming" in standard_name:
        guidance["validation"] = f"Check variable, function, and type names follow {language} conventions"
    elif "testing" in standard_name:
        guidance["validation"] = f"Ensure test structure and patterns match {language} best practices"
    elif "error" in standard_name:
        guidance["validation"] = f"Verify error handling follows {language} idiomatic patterns"

    return guidance


def main():
    """Command-line interface for the no3sis standard tool."""
    if len(sys.argv) < 3:
        print(json.dumps({
            "error": "Usage: no3sis_standard.py <standard_name> <language>",
            "example": "no3sis_standard.py naming-conventions rust",
            "available_languages": list_available_languages()
        }, indent=2))
        sys.exit(1)

    standard_name = sys.argv[1]
    language = sys.argv[2]

    result = get_standard(standard_name, language)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()