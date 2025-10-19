"""
TypeScript Specialist Agent Tools

Core tools for TypeScript/JavaScript analysis, type safety checking,
framework pattern analysis, and build optimization.
"""

# Core analysis tools
from .typescript_analysis_tools import (
    analyze_typescript_code,
    check_eslint_compliance,
    suggest_refactors
)

# Type system tools
from .type_system_tools import (
    analyze_type_safety,
    suggest_type_improvements,
    check_strict_mode
)

# Framework-specific tools
from .framework_tools import (
    analyze_react_patterns,
    analyze_node_patterns,
    suggest_state_management
)

# Testing tools
from .testing_tools import (
    analyze_test_coverage,
    generate_test_stubs,
    suggest_test_patterns
)

# Build optimization tools
from .build_tools import (
    optimize_build_config,
    analyze_bundle_size
)

# Synapse integration
from .no3sis_integration import (
    query_typescript_patterns,
    search_typescript_standards
)

__all__ = [
    # Analysis tools
    "analyze_typescript_code",
    "check_eslint_compliance",
    "suggest_refactors",

    # Type system tools
    "analyze_type_safety",
    "suggest_type_improvements",
    "check_strict_mode",

    # Framework tools
    "analyze_react_patterns",
    "analyze_node_patterns",
    "suggest_state_management",

    # Testing tools
    "analyze_test_coverage",
    "generate_test_stubs",
    "suggest_test_patterns",

    # Build tools
    "optimize_build_config",
    "analyze_bundle_size",

    # Synapse integration
    "query_typescript_patterns",
    "search_typescript_standards"
]