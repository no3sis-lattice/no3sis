"""
Documentation Generation Tools

Core functionality for generating and maintaining documentation.
"""

import os
import re
import ast
import asyncio
from pathlib import Path
from typing import Dict, Any, List, Optional
import json


async def generate_docs(file_path: str, doc_type: str = "auto") -> Dict[str, Any]:
    """
    Generate documentation for a code file.

    Args:
        file_path: Path to file to document
        doc_type: Type of documentation (auto, api, readme, comments)

    Returns:
        Dict with generated documentation
    """
    try:
        path = Path(file_path)

        if not path.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ File not found: {file_path}"
                }],
                "success": False,
                "error": "file_not_found"
            }

        # Read file content
        content = path.read_text(encoding='utf-8')

        # Determine documentation type based on file extension
        if doc_type == "auto":
            doc_type = _determine_doc_type(path.suffix)

        # Generate documentation based on type
        if doc_type == "api":
            docs = await _generate_api_docs(content, path)
        elif doc_type == "readme":
            docs = await _generate_readme(content, path)
        elif doc_type == "comments":
            docs = await _extract_inline_docs(content, path)
        else:
            docs = await _generate_general_docs(content, path)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Generated {doc_type} documentation for {path.name}"
            }],
            "success": True,
            "documentation": docs,
            "doc_type": doc_type,
            "file_analyzed": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to generate docs for {file_path}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def extract_comments(file_path: str) -> Dict[str, Any]:
    """
    Extract existing comments and docstrings from code.

    Args:
        file_path: Path to code file

    Returns:
        Dict with extracted comments and documentation
    """
    try:
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')

        comments = _extract_comments_by_language(content, path.suffix)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Extracted {len(comments)} comments from {path.name}"
            }],
            "success": True,
            "comments": comments,
            "file_path": str(path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to extract comments: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def create_readme(project_path: str, template: Optional[str] = None) -> Dict[str, Any]:
    """
    Create a README file for a project.

    Args:
        project_path: Path to project directory
        template: Optional template to use

    Returns:
        Dict with README content and generation status
    """
    try:
        project_dir = Path(project_path)

        if not project_dir.is_dir():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Directory not found: {project_path}"
                }],
                "success": False,
                "error": "directory_not_found"
            }

        # Analyze project structure
        project_info = await _analyze_project(project_dir)

        # Generate README content
        readme_content = await _generate_readme_content(project_info, template)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Generated README for {project_dir.name}"
            }],
            "success": True,
            "readme_content": readme_content,
            "project_info": project_info,
            "template_used": template
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to create README: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def analyze_code_structure(directory_path: str) -> Dict[str, Any]:
    """
    Analyze code structure for documentation purposes.

    Args:
        directory_path: Path to analyze

    Returns:
        Dict with code structure analysis
    """
    try:
        dir_path = Path(directory_path)
        structure = {}

        # Walk through directory
        for file_path in dir_path.rglob("*"):
            if file_path.is_file() and _is_code_file(file_path):
                relative_path = file_path.relative_to(dir_path)
                structure[str(relative_path)] = await _analyze_file_structure(file_path)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Analyzed structure of {len(structure)} code files"
            }],
            "success": True,
            "structure": structure,
            "directory": str(dir_path)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to analyze structure: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


def _determine_doc_type(file_extension: str) -> str:
    """Determine documentation type based on file extension."""
    api_extensions = {'.py', '.js', '.ts', '.java', '.go', '.rs'}

    if file_extension in api_extensions:
        return "api"
    elif file_extension == '.md':
        return "readme"
    else:
        return "general"


async def _generate_api_docs(content: str, path: Path) -> str:
    """Generate API documentation from code."""
    docs = []

    if path.suffix == '.py':
        docs = _parse_python_api(content)
    elif path.suffix in ['.js', '.ts']:
        docs = _parse_javascript_api(content)
    else:
        docs = _parse_generic_api(content)

    return "\n".join(docs)


async def _generate_readme(content: str, path: Path) -> str:
    """Generate README documentation."""
    return f"""# {path.stem.title()}

## Overview
{_extract_description(content)}

## Usage
{_extract_usage_examples(content)}

## API
{_extract_main_functions(content)}
"""


async def _extract_inline_docs(content: str, path: Path) -> str:
    """Extract inline documentation and comments."""
    comments = _extract_comments_by_language(content, path.suffix)
    return "\n".join(f"- {comment}" for comment in comments)


async def _generate_general_docs(content: str, path: Path) -> str:
    """Generate general documentation."""
    return f"""# Documentation for {path.name}

## File Overview
{_get_file_summary(content)}

## Key Components
{_extract_key_components(content)}
"""


def _extract_comments_by_language(content: str, extension: str) -> List[str]:
    """Extract comments based on file language."""
    comments = []

    if extension == '.py':
        # Python comments and docstrings
        for line in content.split('\n'):
            line = line.strip()
            if line.startswith('#'):
                comments.append(line[1:].strip())
            elif '"""' in line or "'''" in line:
                comments.append(line)

    elif extension in ['.js', '.ts']:
        # JavaScript/TypeScript comments
        for line in content.split('\n'):
            line = line.strip()
            if line.startswith('//'):
                comments.append(line[2:].strip())
            elif line.startswith('/*') or line.startswith('*'):
                comments.append(line)

    return comments


def _is_code_file(path: Path) -> bool:
    """Check if file is a code file."""
    code_extensions = {'.py', '.js', '.ts', '.tsx', '.jsx', '.rs', '.go', '.java', '.cpp', '.c', '.h'}
    return path.suffix in code_extensions


async def _analyze_file_structure(file_path: Path) -> Dict[str, Any]:
    """Analyze structure of a single file."""
    try:
        content = file_path.read_text(encoding='utf-8')

        return {
            "functions": _count_functions(content, file_path.suffix),
            "classes": _count_classes(content, file_path.suffix),
            "lines": len(content.split('\n')),
            "comments": len(_extract_comments_by_language(content, file_path.suffix))
        }
    except:
        return {"error": "Could not analyze file"}


def _count_functions(content: str, extension: str) -> int:
    """Count functions in code."""
    if extension == '.py':
        return len(re.findall(r'^\s*def\s+\w+', content, re.MULTILINE))
    elif extension in ['.js', '.ts']:
        return len(re.findall(r'function\s+\w+|^\s*\w+\s*:\s*function|\w+\s*=>', content, re.MULTILINE))
    return 0


def _count_classes(content: str, extension: str) -> int:
    """Count classes in code."""
    if extension == '.py':
        return len(re.findall(r'^\s*class\s+\w+', content, re.MULTILINE))
    elif extension in ['.js', '.ts']:
        return len(re.findall(r'class\s+\w+', content, re.MULTILINE))
    return 0


async def _analyze_project(project_dir: Path) -> Dict[str, Any]:
    """Analyze project for README generation."""
    return {
        "name": project_dir.name,
        "has_package_json": (project_dir / "package.json").exists(),
        "has_pyproject": (project_dir / "pyproject.toml").exists(),
        "has_cargo": (project_dir / "Cargo.toml").exists(),
        "main_files": [f.name for f in project_dir.iterdir() if f.is_file()],
        "languages": _detect_languages(project_dir)
    }


def _detect_languages(project_dir: Path) -> List[str]:
    """Detect programming languages in project."""
    languages = set()

    for file_path in project_dir.rglob("*"):
        if file_path.suffix == '.py':
            languages.add("Python")
        elif file_path.suffix in ['.js', '.ts']:
            languages.add("JavaScript/TypeScript")
        elif file_path.suffix == '.rs':
            languages.add("Rust")
        elif file_path.suffix == '.go':
            languages.add("Go")

    return list(languages)


async def _generate_readme_content(project_info: Dict, template: Optional[str]) -> str:
    """Generate README content based on project analysis."""
    name = project_info["name"]
    languages = ", ".join(project_info["languages"]) if project_info["languages"] else "Multiple"

    return f"""# {name}

## Overview
A {languages} project.

## Installation
{_generate_install_instructions(project_info)}

## Usage
{_generate_usage_instructions(project_info)}

## Development
{_generate_dev_instructions(project_info)}

## License
MIT
"""


def _generate_install_instructions(project_info: Dict) -> str:
    """Generate installation instructions."""
    if project_info["has_package_json"]:
        return "```bash\nnpm install\n```"
    elif project_info["has_pyproject"]:
        return "```bash\npip install -e .\n```"
    elif project_info["has_cargo"]:
        return "```bash\ncargo build\n```"
    else:
        return "Installation instructions not detected."


def _generate_usage_instructions(project_info: Dict) -> str:
    """Generate usage instructions."""
    return "```bash\n# Add usage examples here\n```"


def _generate_dev_instructions(project_info: Dict) -> str:
    """Generate development instructions."""
    return "```bash\n# Add development setup instructions here\n```"


def _parse_python_api(content: str) -> List[str]:
    """Parse Python API from content."""
    docs = []
    for line in content.split('\n'):
        if line.strip().startswith('def '):
            docs.append(f"### {line.strip()}")
    return docs


def _parse_javascript_api(content: str) -> List[str]:
    """Parse JavaScript API from content."""
    docs = []
    for line in content.split('\n'):
        if 'function' in line:
            docs.append(f"### {line.strip()}")
    return docs


def _parse_generic_api(content: str) -> List[str]:
    """Parse generic API from content."""
    return ["API documentation not available for this file type."]


def _extract_description(content: str) -> str:
    """Extract description from content."""
    return "Description not available."


def _extract_usage_examples(content: str) -> str:
    """Extract usage examples from content."""
    return "Usage examples not available."


def _extract_main_functions(content: str) -> str:
    """Extract main functions from content."""
    return "Function documentation not available."


def _get_file_summary(content: str) -> str:
    """Get file summary."""
    return f"File contains {len(content.split())} words and {len(content.split('\n'))} lines."


def _extract_key_components(content: str) -> str:
    """Extract key components from content."""
    return "Key components not identified."