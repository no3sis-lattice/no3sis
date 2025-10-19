"""
Content Processing and Formatting Tools

Tools for processing and formatting documentation content.
"""

import re
import json
import asyncio
from typing import Dict, Any, List, Optional
from pathlib import Path


async def format_content(content: str, format_type: str = "markdown") -> Dict[str, Any]:
    """
    Format content in specified format.

    Args:
        content: Raw content to format
        format_type: Target format (markdown, html, rst, plain)

    Returns:
        Dict with formatted content
    """
    try:
        if format_type.lower() == "markdown":
            formatted = _format_as_markdown(content)
        elif format_type.lower() == "html":
            formatted = _format_as_html(content)
        elif format_type.lower() == "rst":
            formatted = _format_as_rst(content)
        else:  # plain
            formatted = _format_as_plain(content)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Formatted content as {format_type}"
            }],
            "success": True,
            "formatted_content": formatted,
            "original_length": len(content),
            "formatted_length": len(formatted)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to format content: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def validate_markdown(content: str) -> Dict[str, Any]:
    """
    Validate markdown content for common issues.

    Args:
        content: Markdown content to validate

    Returns:
        Dict with validation results and suggestions
    """
    try:
        issues = []
        suggestions = []

        # Check for common markdown issues
        issues.extend(_check_heading_structure(content))
        issues.extend(_check_link_format(content))
        issues.extend(_check_code_blocks(content))
        issues.extend(_check_list_format(content))

        # Generate suggestions based on issues
        if issues:
            suggestions = _generate_markdown_suggestions(issues)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Validated markdown - Found {len(issues)} issues"
            }],
            "success": len(issues) == 0,
            "issues": issues,
            "suggestions": suggestions,
            "valid": len(issues) == 0
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to validate markdown: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def generate_api_docs(code_content: str, language: str) -> Dict[str, Any]:
    """
    Generate API documentation from code.

    Args:
        code_content: Source code content
        language: Programming language

    Returns:
        Dict with generated API documentation
    """
    try:
        if language.lower() == "python":
            api_docs = _generate_python_api_docs(code_content)
        elif language.lower() in ["javascript", "typescript"]:
            api_docs = _generate_js_api_docs(code_content)
        elif language.lower() == "rust":
            api_docs = _generate_rust_api_docs(code_content)
        else:
            api_docs = _generate_generic_api_docs(code_content)

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Generated API documentation for {language}"
            }],
            "success": True,
            "api_documentation": api_docs,
            "language": language
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to generate API docs: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


def _format_as_markdown(content: str) -> str:
    """Format content as markdown."""
    # Basic markdown formatting
    formatted = content

    # Ensure proper heading hierarchy
    formatted = _fix_heading_hierarchy(formatted)

    # Format code blocks
    formatted = _format_code_blocks(formatted)

    # Clean up whitespace
    formatted = re.sub(r'\n{3,}', '\n\n', formatted)

    return formatted.strip()


def _format_as_html(content: str) -> str:
    """Format content as HTML."""
    # Convert markdown-like syntax to HTML
    html = content

    # Convert headers
    html = re.sub(r'^# (.*)', r'<h1>\1</h1>', html, flags=re.MULTILINE)
    html = re.sub(r'^## (.*)', r'<h2>\1</h2>', html, flags=re.MULTILINE)
    html = re.sub(r'^### (.*)', r'<h3>\1</h3>', html, flags=re.MULTILINE)

    # Convert code blocks
    html = re.sub(r'```(\w+)?\n(.*?)```', r'<pre><code>\2</code></pre>', html, flags=re.DOTALL)

    # Convert inline code
    html = re.sub(r'`([^`]+)`', r'<code>\1</code>', html)

    # Convert bold and italic
    html = re.sub(r'\*\*(.*?)\*\*', r'<strong>\1</strong>', html)
    html = re.sub(r'\*(.*?)\*', r'<em>\1</em>', html)

    # Convert paragraphs
    html = re.sub(r'\n\n', '</p>\n<p>', html)
    html = f'<p>{html}</p>'

    return html


def _format_as_rst(content: str) -> str:
    """Format content as reStructuredText."""
    rst = content

    # Convert headers to RST format
    rst = re.sub(r'^# (.*)', r'\1\n' + '=' * 50, rst, flags=re.MULTILINE)
    rst = re.sub(r'^## (.*)', r'\1\n' + '-' * 30, rst, flags=re.MULTILINE)
    rst = re.sub(r'^### (.*)', r'\1\n' + '^' * 20, rst, flags=re.MULTILINE)

    # Convert code blocks
    rst = re.sub(r'```(\w+)?\n(.*?)```', r'::\n\n    \2', rst, flags=re.DOTALL)

    # Convert inline code
    rst = re.sub(r'`([^`]+)`', r'``\1``', rst)

    return rst


def _format_as_plain(content: str) -> str:
    """Format content as plain text."""
    plain = content

    # Remove markdown syntax
    plain = re.sub(r'^#+\s*', '', plain, flags=re.MULTILINE)  # Headers
    plain = re.sub(r'```.*?```', '', plain, flags=re.DOTALL)  # Code blocks
    plain = re.sub(r'`([^`]+)`', r'\1', plain)  # Inline code
    plain = re.sub(r'\*\*(.*?)\*\*', r'\1', plain)  # Bold
    plain = re.sub(r'\*(.*?)\*', r'\1', plain)  # Italic
    plain = re.sub(r'\[(.*?)\]\(.*?\)', r'\1', plain)  # Links

    return plain.strip()


def _check_heading_structure(content: str) -> List[str]:
    """Check for heading structure issues."""
    issues = []
    lines = content.split('\n')
    prev_level = 0

    for i, line in enumerate(lines):
        if line.startswith('#'):
            level = len(line) - len(line.lstrip('#'))

            if level > prev_level + 1:
                issues.append(f"Line {i+1}: Heading level jumps from {prev_level} to {level}")

            prev_level = level

    return issues


def _check_link_format(content: str) -> List[str]:
    """Check for link formatting issues."""
    issues = []

    # Find malformed links
    malformed_links = re.findall(r'\[([^\]]*)\]\([^)]*\)', content)

    for link in malformed_links:
        if not link.strip():
            issues.append("Empty link text found")

    return issues


def _check_code_blocks(content: str) -> List[str]:
    """Check for code block issues."""
    issues = []

    # Count opening and closing code blocks
    opening_blocks = content.count('```')

    if opening_blocks % 2 != 0:
        issues.append("Unmatched code block markers (```)")

    return issues


def _check_list_format(content: str) -> List[str]:
    """Check for list formatting issues."""
    issues = []
    lines = content.split('\n')

    for i, line in enumerate(lines):
        stripped = line.lstrip()

        # Check for inconsistent list markers
        if stripped.startswith(('- ', '* ', '+ ')):
            if not line.startswith((' ', '-', '*', '+')):
                continue  # This is fine, it's a root level list item

        # Check for numbered lists
        elif re.match(r'^\s*\d+\.', line):
            continue  # Numbered lists are fine

    return issues


def _generate_markdown_suggestions(issues: List[str]) -> List[str]:
    """Generate suggestions based on markdown issues."""
    suggestions = []

    for issue in issues:
        if "Heading level jumps" in issue:
            suggestions.append("Use sequential heading levels (don't skip from # to ###)")
        elif "Empty link text" in issue:
            suggestions.append("Provide descriptive text for all links")
        elif "Unmatched code block" in issue:
            suggestions.append("Ensure all code blocks have matching ``` markers")

    return list(set(suggestions))  # Remove duplicates


def _fix_heading_hierarchy(content: str) -> str:
    """Fix heading hierarchy in markdown."""
    lines = content.split('\n')
    fixed_lines = []
    current_level = 0

    for line in lines:
        if line.startswith('#'):
            level = len(line) - len(line.lstrip('#'))

            # Don't allow jumping more than one level
            if level > current_level + 1:
                level = current_level + 1
                line = '#' * level + line.lstrip('#')

            current_level = level

        fixed_lines.append(line)

    return '\n'.join(fixed_lines)


def _format_code_blocks(content: str) -> str:
    """Format code blocks properly."""
    # Ensure code blocks have language hints where possible
    content = re.sub(r'```\n(def |class |import )', r'```python\n\1', content)
    content = re.sub(r'```\n(function |const |let )', r'```javascript\n\1', content)
    content = re.sub(r'```\n(fn |struct |impl )', r'```rust\n\1', content)

    return content


def _generate_python_api_docs(code: str) -> str:
    """Generate API docs for Python code."""
    docs = ["# Python API Documentation\n"]

    # Extract classes
    classes = re.findall(r'class\s+(\w+)[^:]*:', code)
    if classes:
        docs.append("## Classes\n")
        for cls in classes:
            docs.append(f"### {cls}\n")

    # Extract functions
    functions = re.findall(r'def\s+(\w+)\([^)]*\):', code)
    if functions:
        docs.append("## Functions\n")
        for func in functions:
            if not func.startswith('_'):  # Skip private functions
                docs.append(f"### {func}()\n")

    return '\n'.join(docs)


def _generate_js_api_docs(code: str) -> str:
    """Generate API docs for JavaScript/TypeScript code."""
    docs = ["# JavaScript/TypeScript API Documentation\n"]

    # Extract classes
    classes = re.findall(r'class\s+(\w+)', code)
    if classes:
        docs.append("## Classes\n")
        for cls in classes:
            docs.append(f"### {cls}\n")

    # Extract functions
    functions = re.findall(r'function\s+(\w+)|(\w+)\s*:\s*function|const\s+(\w+)\s*=', code)
    func_names = [name for group in functions for name in group if name]
    if func_names:
        docs.append("## Functions\n")
        for func in func_names:
            docs.append(f"### {func}()\n")

    return '\n'.join(docs)


def _generate_rust_api_docs(code: str) -> str:
    """Generate API docs for Rust code."""
    docs = ["# Rust API Documentation\n"]

    # Extract structs
    structs = re.findall(r'struct\s+(\w+)', code)
    if structs:
        docs.append("## Structs\n")
        for struct in structs:
            docs.append(f"### {struct}\n")

    # Extract functions
    functions = re.findall(r'fn\s+(\w+)', code)
    if functions:
        docs.append("## Functions\n")
        for func in functions:
            docs.append(f"### {func}()\n")

    return '\n'.join(docs)


def _generate_generic_api_docs(code: str) -> str:
    """Generate generic API docs."""
    return f"""# API Documentation

## Overview
This file contains {len(code.split('\n'))} lines of code.

## Structure
- Functions: {len(re.findall(r'function|def|fn ', code))}
- Classes: {len(re.findall(r'class|struct', code))}
"""