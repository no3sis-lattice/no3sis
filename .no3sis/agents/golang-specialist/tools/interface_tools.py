"""
Go Interface Analysis Tools

Specialized tools for analyzing Go interface design, satisfaction patterns,
and composition. Focuses on Go's unique implicit interface satisfaction.
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Set, Tuple


def analyze_interfaces(file_path: str, check_satisfaction: bool, config: Dict[str, Any]) -> str:
    """
    Analyze interface design and usage patterns.

    Args:
        file_path: Path to the Go file containing interfaces
        check_satisfaction: Whether to check interface satisfaction
        config: Agent configuration

    Returns:
        Detailed interface analysis report
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        analysis = {
            "file_path": file_path,
            "interfaces": [],
            "implementations": [],
            "composition_patterns": [],
            "recommendations": []
        }

        # Find interface definitions
        interfaces = _find_interface_definitions(content)
        analysis["interfaces"] = interfaces

        # Find potential implementations (if checking satisfaction)
        if check_satisfaction:
            implementations = _find_interface_implementations(content, interfaces)
            analysis["implementations"] = implementations

        # Check for composition patterns
        composition = _find_composition_patterns(content)
        analysis["composition_patterns"] = composition

        # Generate interface design recommendations
        recommendations = _generate_interface_recommendations(content, interfaces, config)
        analysis["recommendations"] = recommendations

        return _format_interface_report(analysis, config)

    except Exception as e:
        return f"❌ Interface analysis failed: {str(e)}"


def check_interface_satisfaction(interface_name: str, directory: str, config: Dict[str, Any]) -> str:
    """
    Check which types satisfy a given interface across a directory.

    Args:
        interface_name: Name of the interface to check
        directory: Directory to search for implementations
        config: Agent configuration

    Returns:
        Interface satisfaction report
    """
    try:
        if not os.path.exists(directory):
            return f"❌ Directory not found: {directory}"

        satisfaction_analysis = {
            "interface_name": interface_name,
            "directory": directory,
            "interface_definition": None,
            "satisfying_types": [],
            "partial_implementations": [],
            "files_checked": 0
        }

        # Find the interface definition first
        interface_def = _find_interface_in_directory(interface_name, directory)
        if not interface_def:
            return f"❌ Interface '{interface_name}' not found in directory"

        satisfaction_analysis["interface_definition"] = interface_def

        # Check all Go files for implementations
        go_files = _find_go_files_in_directory(directory)
        satisfaction_analysis["files_checked"] = len(go_files)

        for file_path in go_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()

                # Find types that might implement the interface
                satisfying_types = _check_type_satisfaction(content, interface_def, file_path)
                satisfaction_analysis["satisfying_types"].extend(satisfying_types)

                # Find partial implementations
                partial = _find_partial_implementations(content, interface_def, file_path)
                satisfaction_analysis["partial_implementations"].extend(partial)

            except Exception as e:
                print(f"⚠️ Error analyzing {file_path}: {e}")

        return _format_satisfaction_report(satisfaction_analysis, config)

    except Exception as e:
        return f"❌ Interface satisfaction check failed: {str(e)}"


def suggest_interface_design(file_path: str, minimize: bool, config: Dict[str, Any]) -> str:
    """
    Suggest interface design improvements following Go best practices.

    Args:
        file_path: Path to the Go file with interfaces
        minimize: Whether to suggest minimal interfaces
        config: Agent configuration

    Returns:
        Interface design recommendations with examples
    """
    try:
        if not os.path.exists(file_path):
            return f"❌ File not found: {file_path}"

        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        suggestions = {
            "file_path": file_path,
            "current_interfaces": [],
            "design_improvements": [],
            "composition_suggestions": [],
            "naming_suggestions": []
        }

        # Analyze current interfaces
        interfaces = _find_interface_definitions(content)
        suggestions["current_interfaces"] = interfaces

        # Generate design improvements
        design_improvements = _suggest_design_improvements(interfaces, minimize, config)
        suggestions["design_improvements"] = design_improvements

        # Suggest composition opportunities
        composition_suggestions = _suggest_composition_improvements(interfaces, config)
        suggestions["composition_suggestions"] = composition_suggestions

        # Check naming conventions
        naming_suggestions = _check_interface_naming(interfaces, config)
        suggestions["naming_suggestions"] = naming_suggestions

        return _format_design_suggestions(suggestions, config)

    except Exception as e:
        return f"❌ Interface design analysis failed: {str(e)}"


def _find_interface_definitions(content: str) -> List[Dict[str, Any]]:
    """Find all interface definitions in the content."""
    interfaces = []

    # Pattern to match interface definitions
    interface_pattern = r'type\s+(\w+)\s+interface\s*\{([^}]*)\}'
    matches = re.finditer(interface_pattern, content, re.MULTILINE | re.DOTALL)

    for match in matches:
        interface_name = match.group(1)
        interface_body = match.group(2).strip()
        line_num = content[:match.start()].count('\n') + 1

        # Parse methods from interface body
        methods = _parse_interface_methods(interface_body)

        # Check if interface embeds other interfaces
        embedded = _find_embedded_interfaces(interface_body)

        interfaces.append({
            "name": interface_name,
            "line": line_num,
            "methods": methods,
            "embedded_interfaces": embedded,
            "method_count": len(methods),
            "is_exported": interface_name[0].isupper(),
            "body": interface_body
        })

    return interfaces


def _parse_interface_methods(interface_body: str) -> List[Dict[str, Any]]:
    """Parse method signatures from interface body."""
    methods = []
    lines = interface_body.split('\n')

    for line in lines:
        line = line.strip()
        if not line or line.startswith('//'):
            continue

        # Skip embedded interfaces (they don't have parentheses)
        if '(' not in line:
            continue

        # Parse method signature
        method_match = re.match(r'(\w+)\s*\(([^)]*)\)(?:\s*\(([^)]*)\))?(?:\s*(\w+))?', line)
        if method_match:
            method_name = method_match.group(1)
            params = method_match.group(2) if method_match.group(2) else ""
            returns = method_match.group(3) if method_match.group(3) else method_match.group(4) or ""

            methods.append({
                "name": method_name,
                "parameters": params.strip(),
                "returns": returns.strip(),
                "is_exported": method_name[0].isupper(),
                "signature": line
            })

    return methods


def _find_embedded_interfaces(interface_body: str) -> List[str]:
    """Find embedded interfaces in the interface body."""
    embedded = []
    lines = interface_body.split('\n')

    for line in lines:
        line = line.strip()
        if not line or line.startswith('//'):
            continue

        # If line doesn't contain parentheses, it might be an embedded interface
        if '(' not in line and re.match(r'^\w+$', line):
            embedded.append(line)

    return embedded


def _find_interface_implementations(content: str, interfaces: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Find types that potentially implement the interfaces."""
    implementations = []

    # Find all method definitions
    method_pattern = r'func\s+(?:\([^)]+\)\s+)?(\w+)\s*\([^)]*\)'
    method_matches = re.findall(method_pattern, content)

    # Find all type definitions
    type_pattern = r'type\s+(\w+)\s+(?:struct|\w+)'
    type_matches = re.findall(type_pattern, content)

    for interface in interfaces:
        for type_name in type_matches:
            # Check if this type has methods that match the interface
            matching_methods = []
            for method in interface['methods']:
                if method['name'] in method_matches:
                    matching_methods.append(method['name'])

            if len(matching_methods) == len(interface['methods']) and matching_methods:
                implementations.append({
                    "type_name": type_name,
                    "interface_name": interface['name'],
                    "matching_methods": matching_methods,
                    "satisfaction_level": "complete"
                })
            elif matching_methods:
                implementations.append({
                    "type_name": type_name,
                    "interface_name": interface['name'],
                    "matching_methods": matching_methods,
                    "missing_methods": [m['name'] for m in interface['methods'] if m['name'] not in matching_methods],
                    "satisfaction_level": "partial"
                })

    return implementations


def _find_composition_patterns(content: str) -> List[Dict[str, Any]]:
    """Find interface composition patterns."""
    patterns = []

    # Find interfaces that embed other interfaces
    interface_pattern = r'type\s+(\w+)\s+interface\s*\{([^}]*)\}'
    matches = re.finditer(interface_pattern, content, re.MULTILINE | re.DOTALL)

    for match in matches:
        interface_name = match.group(1)
        interface_body = match.group(2).strip()
        embedded = _find_embedded_interfaces(interface_body)

        if embedded:
            patterns.append({
                "interface_name": interface_name,
                "embedded_interfaces": embedded,
                "pattern_type": "embedding",
                "complexity_score": len(embedded)
            })

    return patterns


def _generate_interface_recommendations(content: str, interfaces: List[Dict[str, Any]], config: Dict[str, Any]) -> List[str]:
    """Generate recommendations for interface design."""
    recommendations = []

    for interface in interfaces:
        method_count = interface['method_count']

        # Check method count
        if method_count > 5:
            recommendations.append(
                f"Interface '{interface['name']}' has {method_count} methods. "
                "Consider breaking it into smaller, focused interfaces."
            )

        # Check for non-exported interfaces with exported methods
        if not interface['is_exported']:
            exported_methods = [m for m in interface['methods'] if m['is_exported']]
            if exported_methods:
                recommendations.append(
                    f"Interface '{interface['name']}' is unexported but has exported methods. "
                    "Consider making the interface exported or methods unexported."
                )

        # Check for empty interfaces
        if method_count == 0 and not interface['embedded_interfaces']:
            recommendations.append(
                f"Interface '{interface['name']}' is empty. "
                "Consider using interface{} directly or define specific methods."
            )

    return recommendations


def _find_interface_in_directory(interface_name: str, directory: str) -> Optional[Dict[str, Any]]:
    """Find interface definition in directory."""
    go_files = _find_go_files_in_directory(directory)

    for file_path in go_files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()

            interfaces = _find_interface_definitions(content)
            for interface in interfaces:
                if interface['name'] == interface_name:
                    interface['file_path'] = file_path
                    return interface

        except Exception:
            continue

    return None


def _find_go_files_in_directory(directory: str) -> List[str]:
    """Find all Go files in directory recursively."""
    go_files = []
    path = Path(directory)

    for file_path in path.rglob("*.go"):
        if not file_path.name.endswith('_test.go'):  # Skip test files for implementation checking
            go_files.append(str(file_path))

    return go_files


def _check_type_satisfaction(content: str, interface_def: Dict[str, Any], file_path: str) -> List[Dict[str, Any]]:
    """Check if types in content satisfy the interface."""
    satisfying_types = []

    # Find all type definitions
    type_pattern = r'type\s+(\w+)\s+(?:struct\s*\{|\w+)'
    type_matches = re.findall(type_pattern, content)

    for type_name in type_matches:
        # Find methods for this type
        method_pattern = rf'func\s+\([^)]*\s+{re.escape(type_name)}[^)]*\)\s+(\w+)'
        type_methods = re.findall(method_pattern, content)

        # Check if all interface methods are implemented
        required_methods = {method['name'] for method in interface_def['methods']}
        implemented_methods = set(type_methods)

        if required_methods.issubset(implemented_methods):
            satisfying_types.append({
                "type_name": type_name,
                "file_path": file_path,
                "implemented_methods": list(implemented_methods),
                "interface_methods": list(required_methods),
                "satisfaction_level": "complete"
            })

    return satisfying_types


def _find_partial_implementations(content: str, interface_def: Dict[str, Any], file_path: str) -> List[Dict[str, Any]]:
    """Find types that partially implement the interface."""
    partial_implementations = []

    type_pattern = r'type\s+(\w+)\s+(?:struct\s*\{|\w+)'
    type_matches = re.findall(type_pattern, content)

    for type_name in type_matches:
        method_pattern = rf'func\s+\([^)]*\s+{re.escape(type_name)}[^)]*\)\s+(\w+)'
        type_methods = set(re.findall(method_pattern, content))

        required_methods = {method['name'] for method in interface_def['methods']}
        implemented_methods = type_methods.intersection(required_methods)
        missing_methods = required_methods - type_methods

        if implemented_methods and missing_methods:
            partial_implementations.append({
                "type_name": type_name,
                "file_path": file_path,
                "implemented_methods": list(implemented_methods),
                "missing_methods": list(missing_methods),
                "completion_percentage": len(implemented_methods) / len(required_methods) * 100
            })

    return partial_implementations


def _suggest_design_improvements(interfaces: List[Dict[str, Any]], minimize: bool, config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Suggest interface design improvements."""
    improvements = []

    for interface in interfaces:
        suggestions = []

        # Too many methods
        if interface['method_count'] > 3 and minimize:
            suggestions.append({
                "type": "size_reduction",
                "priority": "high",
                "description": "Consider splitting into smaller, focused interfaces",
                "before": f"type {interface['name']} interface {{ // {interface['method_count']} methods }}",
                "after": f"// Split into focused interfaces:\\ntype Reader interface {{ Read() }}\\ntype Writer interface {{ Write() }}"
            })

        # Method naming
        for method in interface['methods']:
            if not method['is_exported'] and interface['is_exported']:
                suggestions.append({
                    "type": "method_visibility",
                    "priority": "medium",
                    "description": f"Method '{method['name']}' should be exported in exported interface",
                    "suggestion": f"Rename to '{method['name'].capitalize()}'"
                })

        if suggestions:
            improvements.append({
                "interface_name": interface['name'],
                "suggestions": suggestions
            })

    return improvements


def _suggest_composition_improvements(interfaces: List[Dict[str, Any]], config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Suggest composition improvements."""
    suggestions = []

    # Find interfaces that could benefit from composition
    for i, interface1 in enumerate(interfaces):
        for j, interface2 in enumerate(interfaces[i+1:], i+1):
            # Check for common methods
            methods1 = {m['name'] for m in interface1['methods']}
            methods2 = {m['name'] for m in interface2['methods']}
            common_methods = methods1.intersection(methods2)

            if len(common_methods) >= 2:  # At least 2 common methods
                suggestions.append({
                    "type": "extract_common_interface",
                    "interfaces": [interface1['name'], interface2['name']],
                    "common_methods": list(common_methods),
                    "suggested_name": "Common" + interface1['name'].replace("Interface", ""),
                    "description": f"Extract common methods into a shared interface"
                })

    return suggestions


def _check_interface_naming(interfaces: List[Dict[str, Any]], config: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Check interface naming conventions."""
    suggestions = []

    for interface in interfaces:
        name = interface['name']

        # Check for -er suffix for single-method interfaces
        if interface['method_count'] == 1 and not name.endswith('er'):
            method_name = interface['methods'][0]['name']
            suggested_name = method_name + 'er' if not method_name.endswith('e') else method_name + 'r'
            
            suggestions.append({
                "interface_name": name,
                "type": "naming_convention",
                "description": "Single-method interfaces should typically end with 'er'",
                "suggested_name": suggested_name.capitalize(),
                "method": method_name
            })

        # Check for Interface suffix (anti-pattern in Go)
        if name.endswith('Interface'):
            suggested_name = name.replace('Interface', '')
            suggestions.append({
                "interface_name": name,
                "type": "interface_suffix",
                "description": "Avoid 'Interface' suffix in Go interface names",
                "suggested_name": suggested_name
            })

    return suggestions


def _format_interface_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the interface analysis report."""
    report = "# Interface Analysis Report\n\n"
    report += f"**File:** `{analysis['file_path']}`\n\n"

    # Interfaces found
    interfaces = analysis['interfaces']
    report += f"## Interfaces Found ({len(interfaces)})\n\n"

    for interface in interfaces:
        export_status = "exported" if interface['is_exported'] else "unexported"
        report += f"### `{interface['name']}` ({export_status})\n"
        report += f"- **Line:** {interface['line']}\n"
        report += f"- **Methods:** {interface['method_count']}\n"
        
        if interface['embedded_interfaces']:
            report += f"- **Embeds:** {', '.join(interface['embedded_interfaces'])}\n"
        
        if interface['methods']:
            report += f"- **Method signatures:**\n"
            for method in interface['methods']:
                export_icon = "🔓" if method['is_exported'] else "🔒"
                report += f"  - {export_icon} `{method['signature']}`\n"
        
        report += "\n"

    # Implementations
    implementations = analysis['implementations']
    if implementations:
        report += f"## Implementations Found ({len(implementations)})\n\n"
        
        complete = [impl for impl in implementations if impl['satisfaction_level'] == 'complete']
        partial = [impl for impl in implementations if impl['satisfaction_level'] == 'partial']
        
        if complete:
            report += "### Complete Implementations\n"
            for impl in complete:
                report += f"- `{impl['type_name']}` implements `{impl['interface_name']}`\n"
        
        if partial:
            report += "\n### Partial Implementations\n"
            for impl in partial:
                report += f"- `{impl['type_name']}` partially implements `{impl['interface_name']}`\n"
                report += f"  - Missing: {', '.join(impl['missing_methods'])}\n"
        
        report += "\n"

    # Composition patterns
    composition = analysis['composition_patterns']
    if composition:
        report += f"## Composition Patterns ({len(composition)})\n\n"
        for pattern in composition:
            report += f"- `{pattern['interface_name']}` embeds: {', '.join(pattern['embedded_interfaces'])}\n"
        report += "\n"

    # Recommendations
    recommendations = analysis['recommendations']
    if recommendations:
        report += "## Recommendations\n\n"
        for rec in recommendations:
            report += f"- 💡 {rec}\n"

    return report


def _format_satisfaction_report(analysis: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the interface satisfaction report."""
    report = "# Interface Satisfaction Report\n\n"
    report += f"**Interface:** `{analysis['interface_name']}`\n"
    report += f"**Directory:** `{analysis['directory']}`\n"
    report += f"**Files Checked:** {analysis['files_checked']}\n\n"

    # Interface definition
    interface_def = analysis['interface_definition']
    if interface_def:
        report += "## Interface Definition\n\n"
        report += f"**File:** `{interface_def.get('file_path', 'unknown')}`\n"
        report += f"**Line:** {interface_def['line']}\n"
        report += f"**Methods:** {interface_def['method_count']}\n\n"
        
        for method in interface_def['methods']:
            report += f"- `{method['signature']}`\n"
        report += "\n"

    # Satisfying types
    satisfying = analysis['satisfying_types']
    if satisfying:
        report += f"## Complete Implementations ({len(satisfying)})\n\n"
        for impl in satisfying:
            report += f"### `{impl['type_name']}` ✅\n"
            report += f"**File:** `{impl['file_path']}`\n"
            report += f"**Methods:** {', '.join(impl['implemented_methods'])}\n\n"

    # Partial implementations
    partial = analysis['partial_implementations']
    if partial:
        report += f"## Partial Implementations ({len(partial)})\n\n"
        for impl in partial:
            completion = impl['completion_percentage']
            progress_bar = "🟩" * int(completion // 20) + "⬜" * (5 - int(completion // 20))
            report += f"### `{impl['type_name']}` ({completion:.1f}%) {progress_bar}\n"
            report += f"**File:** `{impl['file_path']}`\n"
            report += f"**Implemented:** {', '.join(impl['implemented_methods'])}\n"
            report += f"**Missing:** {', '.join(impl['missing_methods'])}\n\n"

    if not satisfying and not partial:
        report += "## No implementations found ❌\n\n"
        report += "Consider:\n"
        report += "- Creating types that implement this interface\n"
        report += "- Checking if the interface is used elsewhere\n"
        report += "- Simplifying the interface if it's too complex\n"

    return report


def _format_design_suggestions(suggestions: Dict[str, Any], config: Dict[str, Any]) -> str:
    """Format the interface design suggestions."""
    report = "# Interface Design Suggestions\n\n"
    report += f"**File:** `{suggestions['file_path']}`\n\n"

    interfaces = suggestions['current_interfaces']
    report += f"## Current Interfaces ({len(interfaces)})\n\n"
    
    for interface in interfaces:
        methods_info = f"{interface['method_count']} methods"
        embedded_info = f", embeds {len(interface['embedded_interfaces'])}" if interface['embedded_interfaces'] else ""
        report += f"- `{interface['name']}`: {methods_info}{embedded_info}\n"
    report += "\n"

    # Design improvements
    improvements = suggestions['design_improvements']
    if improvements:
        report += "## Design Improvements\n\n"
        for improvement in improvements:
            report += f"### `{improvement['interface_name']}`\n\n"
            for suggestion in improvement['suggestions']:
                priority_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(suggestion['priority'], "💡")
                report += f"{priority_icon} **{suggestion['type']}** ({suggestion['priority']} priority)\n"
                report += f"{suggestion['description']}\n\n"
                
                if 'before' in suggestion:
                    report += "**Before:**\n```go\n"
                    report += suggestion['before']
                    report += "\n```\n\n"
                
                if 'after' in suggestion:
                    report += "**After:**\n```go\n"
                    report += suggestion['after']
                    report += "\n```\n\n"
                
                if 'suggestion' in suggestion:
                    report += f"💡 {suggestion['suggestion']}\n\n"

    # Composition suggestions
    composition = suggestions['composition_suggestions']
    if composition:
        report += "## Composition Opportunities\n\n"
        for comp in composition:
            if comp['type'] == 'extract_common_interface':
                report += f"### Extract Common Interface\n"
                report += f"**Interfaces:** {', '.join(comp['interfaces'])}\n"
                report += f"**Common Methods:** {', '.join(comp['common_methods'])}\n"
                report += f"**Suggested Name:** `{comp['suggested_name']}`\n"
                report += f"{comp['description']}\n\n"

    # Naming suggestions
    naming = suggestions['naming_suggestions']
    if naming:
        report += "## Naming Improvements\n\n"
        for name_suggestion in naming:
            icon = "📝" if name_suggestion['type'] == 'naming_convention' else "⚠️"
            report += f"{icon} **{name_suggestion['interface_name']}**\n"
            report += f"{name_suggestion['description']}\n"
            report += f"💡 Suggested: `{name_suggestion['suggested_name']}`\n\n"

    return report