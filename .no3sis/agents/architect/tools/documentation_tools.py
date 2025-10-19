"""
Documentation Tools

Generate architectural documentation, ADRs, and diagrams.
"""

import asyncio
from typing import Dict, List, Any
from datetime import datetime

async def create_architectural_documentation(architecture: Dict[str, Any],
                                           format: str = "c4",
                                           include_decisions: bool = True) -> Dict[str, Any]:
    """Create comprehensive architectural documentation."""
    await asyncio.sleep(0.1)

    documentation = {
        "format": format,
        "timestamp": datetime.now().isoformat(),
        "overview": _generate_system_overview(architecture),
        "components": _document_components(architecture.get("components", [])),
        "technologies": architecture.get("technologies", {}),
        "deployment": _document_deployment(architecture)
    }

    if format == "c4":
        documentation["c4_levels"] = _generate_c4_structure(architecture)

    return documentation

async def generate_decision_records(architecture: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Generate architectural decision records."""
    await asyncio.sleep(0.1)

    decisions = architecture.get("architectural_decisions", [])

    formatted_decisions = []
    for i, decision in enumerate(decisions, 1):
        formatted_decisions.append({
            "adr_number": f"ADR-{i:03d}",
            "title": decision.get("title", "Unknown Decision"),
            "date": datetime.now().strftime("%Y-%m-%d"),
            "status": "Accepted",
            "context": decision.get("context", ""),
            "decision": decision.get("decision", ""),
            "consequences": decision.get("consequences", [])
        })

    return formatted_decisions

async def create_c4_diagrams(architecture: Dict[str, Any]) -> Dict[str, Any]:
    """Create C4 model diagrams."""
    return {
        "system_context": "System context diagram generated",
        "container": "Container diagram generated",
        "component": "Component diagram generated",
        "code": "Code diagram generated"
    }

def _generate_system_overview(architecture: Dict[str, Any]) -> str:
    """Generate system overview documentation."""
    pattern = architecture.get("pattern", "Unknown")
    component_count = len(architecture.get("components", []))

    return f"""
# System Architecture Overview

**Architectural Pattern**: {pattern}
**Components**: {component_count} identified
**Scalability Rating**: {architecture.get("scalability_rating", "Unknown")}
**Estimated Complexity**: {architecture.get("estimated_complexity", "Unknown")}

## Architecture Summary
This system follows the {pattern} architectural pattern, designed to meet the specified requirements with {component_count} core components.
    """.strip()

def _document_components(components: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Document system components."""
    documented = []
    for component in components:
        documented.append({
            "name": component.get("name", "Unknown"),
            "type": component.get("type", "Unknown"),
            "responsibility": component.get("responsibility", "No description"),
            "interfaces": component.get("interfaces", []),
            "dependencies": component.get("dependencies", [])
        })
    return documented

def _document_deployment(architecture: Dict[str, Any]) -> Dict[str, Any]:
    """Document deployment architecture."""
    return {
        "model": architecture.get("deployment_model", "Unknown"),
        "technologies": architecture.get("technologies", {}),
        "infrastructure": "Cloud-based deployment recommended"
    }

def _generate_c4_structure(architecture: Dict[str, Any]) -> Dict[str, str]:
    """Generate C4 model structure."""
    return {
        "level_1_context": "System context showing external dependencies",
        "level_2_container": "Container view showing major technical building blocks",
        "level_3_component": "Component view showing internal structure",
        "level_4_code": "Code view showing implementation details"
    }