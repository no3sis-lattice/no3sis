"""
Architect Tools Package

Comprehensive system design and architecture analysis tools with Synapse integration.
"""

from .system_design import (
    design_system_architecture,
    evaluate_architectural_patterns,
    analyze_scalability_requirements
)

from .technology_assessment import (
    assess_technology_stack,
    compare_technology_options,
    evaluate_stack_compatibility
)

from .documentation_tools import (
    create_architectural_documentation,
    generate_decision_records,
    create_c4_diagrams
)

from .pattern_analysis import (
    analyze_design_patterns,
    recommend_architectural_style,
    evaluate_pattern_trade_offs
)

from .no3sis_integration import (
    get_architectural_patterns,
    search_design_knowledge,
    get_technology_standards
)

from .agent_communication import (
    coordinate_with_development_team,
    request_technical_review,
    collaborate_with_specialists
)

from .config_manager import (
    load_config,
    get_architectural_standards,
    get_design_preferences
)

from .mock_sdk import (
    create_sdk_mcp_server,
    tool,
    query,
    ClaudeCodeSdkMessage
)

__all__ = [
    # System design
    "design_system_architecture",
    "evaluate_architectural_patterns",
    "analyze_scalability_requirements",

    # Technology assessment
    "assess_technology_stack",
    "compare_technology_options",
    "evaluate_stack_compatibility",

    # Documentation
    "create_architectural_documentation",
    "generate_decision_records",
    "create_c4_diagrams",

    # Pattern analysis
    "analyze_design_patterns",
    "recommend_architectural_style",
    "evaluate_pattern_trade_offs",

    # Synapse integration
    "get_architectural_patterns",
    "search_design_knowledge",
    "get_technology_standards",

    # Agent communication
    "coordinate_with_development_team",
    "request_technical_review",
    "collaborate_with_specialists",

    # Configuration
    "load_config",
    "get_architectural_standards",
    "get_design_preferences",

    # SDK fallback
    "create_sdk_mcp_server",
    "tool",
    "query",
    "ClaudeCodeSdkMessage"
]