"""
Rust Specialist Agent Tools

Core tools for Rust analysis, ownership checking, async patterns,
Cargo ecosystem management, and performance optimization.
"""

# Core analysis tools
from .rust_analysis_tools import (
    analyze_rust_code,
    check_clippy_warnings,
    suggest_refactors
)

# Ownership and borrowing tools
from .ownership_tools import (
    analyze_ownership,
    check_lifetimes,
    suggest_borrow_improvements
)

# Cargo and ecosystem tools
from .cargo_tools import (
    analyze_cargo_project,
    check_dependencies,
    optimize_build_config
)

# Async and performance tools
from .async_performance_tools import (
    analyze_async_patterns,
    check_error_handling,
    suggest_performance_improvements
)

# Synapse integration
from .no3sis_integration import (
    query_rust_patterns,
    search_rust_standards
)

__all__ = [
    # Core analysis
    "analyze_rust_code",
    "check_clippy_warnings",
    "suggest_refactors",

    # Ownership tools
    "analyze_ownership",
    "check_lifetimes",
    "suggest_borrow_improvements",

    # Cargo tools
    "analyze_cargo_project",
    "check_dependencies",
    "optimize_build_config",

    # Async and performance
    "analyze_async_patterns",
    "check_error_handling",
    "suggest_performance_improvements",

    # Synapse integration
    "query_rust_patterns",
    "search_rust_standards"
]