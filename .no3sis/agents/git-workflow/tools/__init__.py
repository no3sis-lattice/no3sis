"""
Git Workflow Tools Package

Intelligent git operations with Synapse integration for branch management,
commit operations, and automated workflows.
"""

from .git_operations import (
    manage_branches,
    create_commits,
    handle_merges,
    check_git_status,
    execute_git_command
)

from .workflow_automation import (
    execute_git_workflow,
    create_feature_workflow,
    create_hotfix_workflow,
    create_release_workflow
)

from .pr_management import (
    create_pull_requests,
    generate_pr_description,
    analyze_pr_readiness
)

from .no3sis_integration import (
    get_synapse_standards,
    search_git_patterns,
    get_commit_conventions
)

from .agent_communication import (
    coordinate_workflow_with_agents,
    notify_completion,
    request_code_review
)

from .config_manager import (
    load_config,
    get_git_conventions,
    get_branch_rules
)

from .mock_sdk import (
    create_sdk_mcp_server,
    tool,
    query,
    ClaudeCodeSdkMessage
)

__all__ = [
    # Core git operations
    "manage_branches",
    "create_commits",
    "handle_merges",
    "check_git_status",
    "execute_git_command",

    # Workflow automation
    "execute_git_workflow",
    "create_feature_workflow",
    "create_hotfix_workflow",
    "create_release_workflow",

    # PR management
    "create_pull_requests",
    "generate_pr_description",
    "analyze_pr_readiness",

    # Synapse integration
    "get_synapse_standards",
    "search_git_patterns",
    "get_commit_conventions",

    # Agent communication
    "coordinate_workflow_with_agents",
    "notify_completion",
    "request_code_review",

    # Configuration
    "load_config",
    "get_git_conventions",
    "get_branch_rules",

    # SDK fallback
    "create_sdk_mcp_server",
    "tool",
    "query",
    "ClaudeCodeSdkMessage"
]