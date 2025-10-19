"""
Code Hound Tools Package

Comprehensive code quality analysis and enforcement tools.
"""

from .analysis_tools import (
    deep_code_analysis,
    calculate_complexity_metrics,
    detect_code_smells
)

from .standards_tools import (
    enforce_tdd_standards,
    check_solid_principles,
    detect_dry_violations,
    scan_shortcuts
)

from .quality_tools import (
    calculate_quality_scores,
    generate_review_report,
    format_violations_report
)

from .no3sis_integration import (
    get_synapse_patterns,
    search_knowledge_base,
    get_coding_standards
)

from .agent_communication import (
    notify_language_specialists,
    coordinate_with_agents,
    broadcast_quality_findings
)

from .config_manager import (
    load_config,
    get_quality_thresholds,
    get_enforcement_rules
)

from .mock_sdk import (
    create_sdk_mcp_server,
    tool,
    query,
    ClaudeCodeSdkMessage
)

__all__ = [
    # Analysis tools
    "deep_code_analysis",
    "calculate_complexity_metrics",
    "detect_code_smells",

    # Standards enforcement
    "enforce_tdd_standards",
    "check_solid_principles",
    "detect_dry_violations",
    "scan_shortcuts",

    # Quality assessment
    "calculate_quality_scores",
    "generate_review_report",
    "format_violations_report",

    # Synapse integration
    "get_synapse_patterns",
    "search_knowledge_base",
    "get_coding_standards",

    # Agent communication
    "notify_language_specialists",
    "coordinate_with_agents",
    "broadcast_quality_findings",

    # Configuration
    "load_config",
    "get_quality_thresholds",
    "get_enforcement_rules",

    # SDK fallback
    "create_sdk_mcp_server",
    "tool",
    "query",
    "ClaudeCodeSdkMessage"
]