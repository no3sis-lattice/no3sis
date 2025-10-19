"""
UX Designer Agent Tools

Provides user experience analysis, interface design evaluation, and usability optimization capabilities.
"""

from .usability_tools import (
    analyze_usability,
    evaluate_user_flow,
    assess_accessibility,
    generate_heuristic_evaluation,
    analyze_user_feedback,
    create_usability_report
)

from .design_tools import (
    analyze_visual_hierarchy,
    evaluate_color_scheme,
    assess_typography,
    generate_design_suggestions,
    create_style_guide,
    analyze_layout_patterns
)

from .prototyping_tools import (
    generate_wireframes,
    create_user_stories,
    design_mockups,
    validate_interaction_patterns,
    generate_component_library,
    create_design_system
)

from .research_tools import (
    conduct_user_research,
    analyze_target_audience,
    create_user_personas,
    generate_user_journey_maps,
    analyze_competitive_landscape,
    validate_design_assumptions
)

from .no3sis_integration import query_synapse_design, search_design_patterns
from .mock_sdk import create_sdk_mcp_server, tool, query, ClaudeCodeSdkMessage

__all__ = [
    # Usability analysis
    'analyze_usability',
    'evaluate_user_flow',
    'assess_accessibility',
    'generate_heuristic_evaluation',
    'analyze_user_feedback',
    'create_usability_report',

    # Design evaluation
    'analyze_visual_hierarchy',
    'evaluate_color_scheme',
    'assess_typography',
    'generate_design_suggestions',
    'create_style_guide',
    'analyze_layout_patterns',

    # Prototyping and design
    'generate_wireframes',
    'create_user_stories',
    'design_mockups',
    'validate_interaction_patterns',
    'generate_component_library',
    'create_design_system',

    # User research
    'conduct_user_research',
    'analyze_target_audience',
    'create_user_personas',
    'generate_user_journey_maps',
    'analyze_competitive_landscape',
    'validate_design_assumptions',

    # Integration
    'query_synapse_design',
    'search_design_patterns',

    # SDK
    'create_sdk_mcp_server',
    'tool',
    'query',
    'ClaudeCodeSdkMessage'
]