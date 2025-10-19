"""
Output Parsing and Formatting Tools

Tools for processing and formatting command outputs.
"""

import re
import json
import csv
import xml.etree.ElementTree as ET
from typing import Dict, Any, List, Optional, Union
from io import StringIO


async def parse_output(output: str, format_type: str = "text") -> Dict[str, Any]:
    """
    Parse command output in various formats.

    Args:
        output: Raw output text to parse
        format_type: Format to parse (text, json, csv, xml, lines)

    Returns:
        Dict with parsed output and metadata
    """
    try:
        if format_type.lower() == "json":
            parsed = _parse_json(output)
        elif format_type.lower() == "csv":
            parsed = _parse_csv(output)
        elif format_type.lower() == "xml":
            parsed = _parse_xml(output)
        elif format_type.lower() == "lines":
            parsed = _parse_lines(output)
        elif format_type.lower() == "key_value":
            parsed = _parse_key_value(output)
        elif format_type.lower() == "table":
            parsed = _parse_table(output)
        else:  # default to text
            parsed = {"content": output, "format": "text"}

        return {
            "content": [{
                "type": "text",
                "text": f"✓ Parsed output as {format_type}"
            }],
            "success": True,
            "parsed_data": parsed,
            "original_format": format_type,
            "output_length": len(output)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to parse output as {format_type}: {str(e)}"
            }],
            "success": False,
            "error": str(e),
            "raw_output": output
        }


async def format_results(data: Any, output_format: str = "pretty") -> Dict[str, Any]:
    """
    Format data for display in various formats.

    Args:
        data: Data to format
        output_format: Output format (pretty, json, table, compact)

    Returns:
        Dict with formatted output
    """
    try:
        if output_format.lower() == "json":
            formatted = json.dumps(data, indent=2, default=str)
        elif output_format.lower() == "table":
            formatted = _format_as_table(data)
        elif output_format.lower() == "compact":
            formatted = _format_compact(data)
        else:  # pretty format
            formatted = _format_pretty(data)

        return {
            "content": [{
                "type": "text",
                "text": formatted
            }],
            "success": True,
            "format_used": output_format,
            "data_type": type(data).__name__
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Failed to format data: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


def _parse_json(output: str) -> Dict[str, Any]:
    """Parse JSON output."""
    try:
        # Try to find JSON in the output
        json_match = re.search(r'(\{.*\}|\[.*\])', output, re.DOTALL)
        if json_match:
            json_str = json_match.group(1)
            data = json.loads(json_str)
        else:
            # Try parsing the whole output
            data = json.loads(output.strip())

        return {
            "content": data,
            "format": "json",
            "valid": True
        }
    except json.JSONDecodeError as e:
        return {
            "content": output,
            "format": "json",
            "valid": False,
            "error": str(e)
        }


def _parse_csv(output: str) -> Dict[str, Any]:
    """Parse CSV output."""
    try:
        # Try different delimiters
        delimiters = [',', ';', '\t', '|']
        best_result = None
        max_columns = 0

        for delimiter in delimiters:
            try:
                reader = csv.reader(StringIO(output), delimiter=delimiter)
                rows = list(reader)

                if rows and len(rows[0]) > max_columns:
                    max_columns = len(rows[0])
                    best_result = {
                        "headers": rows[0] if rows else [],
                        "rows": rows[1:] if len(rows) > 1 else [],
                        "delimiter": delimiter,
                        "row_count": len(rows) - 1 if len(rows) > 1 else 0
                    }
            except:
                continue

        if best_result:
            return {
                "content": best_result,
                "format": "csv",
                "valid": True
            }
        else:
            return {
                "content": output.split('\n'),
                "format": "csv",
                "valid": False,
                "error": "Could not parse as CSV"
            }

    except Exception as e:
        return {
            "content": output,
            "format": "csv",
            "valid": False,
            "error": str(e)
        }


def _parse_xml(output: str) -> Dict[str, Any]:
    """Parse XML output."""
    try:
        root = ET.fromstring(output.strip())
        data = _xml_to_dict(root)

        return {
            "content": data,
            "format": "xml",
            "valid": True,
            "root_tag": root.tag
        }
    except ET.ParseError as e:
        return {
            "content": output,
            "format": "xml",
            "valid": False,
            "error": str(e)
        }


def _parse_lines(output: str) -> Dict[str, Any]:
    """Parse output as separate lines."""
    lines = [line.rstrip() for line in output.split('\n')]
    non_empty_lines = [line for line in lines if line.strip()]

    return {
        "content": {
            "all_lines": lines,
            "non_empty_lines": non_empty_lines,
            "line_count": len(lines),
            "non_empty_count": len(non_empty_lines)
        },
        "format": "lines",
        "valid": True
    }


def _parse_key_value(output: str) -> Dict[str, Any]:
    """Parse key-value pairs from output."""
    pairs = {}
    lines = output.strip().split('\n')

    for line in lines:
        line = line.strip()
        if ':' in line:
            key, value = line.split(':', 1)
            pairs[key.strip()] = value.strip()
        elif '=' in line:
            key, value = line.split('=', 1)
            pairs[key.strip()] = value.strip()

    return {
        "content": pairs,
        "format": "key_value",
        "valid": len(pairs) > 0,
        "pair_count": len(pairs)
    }


def _parse_table(output: str) -> Dict[str, Any]:
    """Parse tabular data from output."""
    lines = [line.strip() for line in output.split('\n') if line.strip()]

    if not lines:
        return {"content": [], "format": "table", "valid": False}

    # Try to detect table structure
    # Look for lines with consistent spacing or separators
    rows = []
    for line in lines:
        # Skip separator lines (like -----)
        if re.match(r'^[-+|=\s]+$', line):
            continue

        # Split on whitespace (2+ spaces) or common separators
        if '|' in line:
            row = [cell.strip() for cell in line.split('|') if cell.strip()]
        else:
            row = re.split(r'\s{2,}', line)

        if row:
            rows.append(row)

    return {
        "content": {
            "headers": rows[0] if rows else [],
            "rows": rows[1:] if len(rows) > 1 else [],
            "row_count": len(rows) - 1 if len(rows) > 1 else 0,
            "column_count": len(rows[0]) if rows else 0
        },
        "format": "table",
        "valid": len(rows) > 0
    }


def _xml_to_dict(element):
    """Convert XML element to dictionary."""
    result = {}

    # Add attributes
    if element.attrib:
        result['@attributes'] = element.attrib

    # Add text content
    if element.text and element.text.strip():
        if len(element) == 0:
            return element.text.strip()
        result['@text'] = element.text.strip()

    # Add child elements
    for child in element:
        child_data = _xml_to_dict(child)
        if child.tag in result:
            if not isinstance(result[child.tag], list):
                result[child.tag] = [result[child.tag]]
            result[child.tag].append(child_data)
        else:
            result[child.tag] = child_data

    return result


def _format_pretty(data: Any) -> str:
    """Format data in a pretty, human-readable way."""
    if isinstance(data, dict):
        return _format_dict_pretty(data)
    elif isinstance(data, list):
        return _format_list_pretty(data)
    else:
        return str(data)


def _format_dict_pretty(data: dict, indent: int = 0) -> str:
    """Format dictionary in a pretty way."""
    result = []
    prefix = "  " * indent

    for key, value in data.items():
        if isinstance(value, dict):
            result.append(f"{prefix}{key}:")
            result.append(_format_dict_pretty(value, indent + 1))
        elif isinstance(value, list):
            result.append(f"{prefix}{key}: [{len(value)} items]")
            if len(value) <= 5:  # Show small lists
                for item in value:
                    result.append(f"{prefix}  - {item}")
        else:
            result.append(f"{prefix}{key}: {value}")

    return "\n".join(result)


def _format_list_pretty(data: list) -> str:
    """Format list in a pretty way."""
    if not data:
        return "[]"

    result = [f"[{len(data)} items]"]
    for i, item in enumerate(data[:10]):  # Show first 10 items
        if isinstance(item, (dict, list)):
            result.append(f"  [{i}]: {type(item).__name__}")
        else:
            result.append(f"  [{i}]: {item}")

    if len(data) > 10:
        result.append(f"  ... and {len(data) - 10} more items")

    return "\n".join(result)


def _format_as_table(data: Any) -> str:
    """Format data as a table if possible."""
    if isinstance(data, dict) and "headers" in data and "rows" in data:
        # Already structured table data
        headers = data["headers"]
        rows = data["rows"]

        if not headers or not rows:
            return str(data)

        # Calculate column widths
        col_widths = [len(str(h)) for h in headers]
        for row in rows:
            for i, cell in enumerate(row):
                if i < len(col_widths):
                    col_widths[i] = max(col_widths[i], len(str(cell)))

        # Format table
        result = []

        # Header
        header_line = " | ".join(str(h).ljust(w) for h, w in zip(headers, col_widths))
        result.append(header_line)
        result.append("-" * len(header_line))

        # Rows
        for row in rows:
            row_line = " | ".join(str(cell).ljust(col_widths[i]) if i < len(col_widths) else str(cell)
                                  for i, cell in enumerate(row))
            result.append(row_line)

        return "\n".join(result)
    else:
        return _format_pretty(data)


def _format_compact(data: Any) -> str:
    """Format data in a compact way."""
    if isinstance(data, dict):
        items = [f"{k}={v}" for k, v in data.items()]
        return "{" + ", ".join(items) + "}"
    elif isinstance(data, list):
        return f"[{len(data)} items: {', '.join(str(x) for x in data[:3])}{'...' if len(data) > 3 else ''}]"
    else:
        return str(data)