"""
DevOps Engineer Agent Tools

Provides infrastructure automation, CI/CD management, and deployment capabilities.
"""

from .infrastructure_tools import (
    manage_containers,
    configure_ci_cd,
    deploy_services,
    monitor_health,
    scan_infrastructure,
    provision_resources
)

from .deployment_tools import (
    create_dockerfile,
    build_image,
    deploy_to_environment,
    manage_secrets,
    validate_deployment
)

from .monitoring_tools import (
    setup_monitoring,
    check_service_health,
    analyze_logs,
    create_alerts,
    generate_reports
)

from .no3sis_integration import query_synapse_devops, search_deployment_patterns
from .mock_sdk import create_sdk_mcp_server, tool, query, ClaudeCodeSdkMessage

__all__ = [
    # Infrastructure tools
    'manage_containers',
    'configure_ci_cd',
    'deploy_services',
    'monitor_health',
    'scan_infrastructure',
    'provision_resources',

    # Deployment tools
    'create_dockerfile',
    'build_image',
    'deploy_to_environment',
    'manage_secrets',
    'validate_deployment',

    # Monitoring tools
    'setup_monitoring',
    'check_service_health',
    'analyze_logs',
    'create_alerts',
    'generate_reports',

    # Integration
    'query_synapse_devops',
    'search_deployment_patterns',

    # SDK
    'create_sdk_mcp_server',
    'tool',
    'query',
    'ClaudeCodeSdkMessage'
]