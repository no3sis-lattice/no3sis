"""
Security Specialist Agent Tools

Provides vulnerability scanning, threat analysis, and security hardening capabilities.
"""

from .vulnerability_tools import (
    scan_vulnerabilities,
    analyze_dependencies,
    check_owasp_compliance,
    detect_secrets,
    audit_permissions,
    validate_security_headers
)

from .threat_modeling_tools import (
    analyze_threats,
    create_threat_model,
    assess_attack_vectors,
    evaluate_risk_score,
    suggest_mitigations,
    document_security_requirements
)

from .hardening_tools import (
    suggest_hardening,
    validate_configuration,
    audit_access_controls,
    check_encryption,
    review_authentication,
    analyze_network_security
)

from .compliance_tools import (
    check_compliance_frameworks,
    generate_security_reports,
    validate_privacy_requirements,
    audit_data_protection,
    assess_regulatory_compliance
)

from .no3sis_integration import query_synapse_security, search_vulnerability_patterns
from .mock_sdk import create_sdk_mcp_server, tool, query, ClaudeCodeSdkMessage

__all__ = [
    # Vulnerability scanning
    'scan_vulnerabilities',
    'analyze_dependencies',
    'check_owasp_compliance',
    'detect_secrets',
    'audit_permissions',
    'validate_security_headers',

    # Threat modeling
    'analyze_threats',
    'create_threat_model',
    'assess_attack_vectors',
    'evaluate_risk_score',
    'suggest_mitigations',
    'document_security_requirements',

    # Security hardening
    'suggest_hardening',
    'validate_configuration',
    'audit_access_controls',
    'check_encryption',
    'review_authentication',
    'analyze_network_security',

    # Compliance
    'check_compliance_frameworks',
    'generate_security_reports',
    'validate_privacy_requirements',
    'audit_data_protection',
    'assess_regulatory_compliance',

    # Integration
    'query_synapse_security',
    'search_vulnerability_patterns',

    # SDK
    'create_sdk_mcp_server',
    'tool',
    'query',
    'ClaudeCodeSdkMessage'
]