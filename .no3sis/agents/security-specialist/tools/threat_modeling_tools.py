"""
Threat modeling and risk analysis tools for comprehensive security assessment.
"""

import json
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from enum import Enum


class ThreatCategory(Enum):
    SPOOFING = "Spoofing"
    TAMPERING = "Tampering"
    REPUDIATION = "Repudiation"
    INFORMATION_DISCLOSURE = "Information Disclosure"
    DENIAL_OF_SERVICE = "Denial of Service"
    ELEVATION_OF_PRIVILEGE = "Elevation of Privilege"


class RiskLevel(Enum):
    LOW = 1
    MEDIUM = 2
    HIGH = 3
    CRITICAL = 4


@dataclass
class ThreatVector:
    name: str
    category: ThreatCategory
    description: str
    likelihood: RiskLevel
    impact: RiskLevel
    assets_at_risk: List[str]
    mitigations: List[str]


async def analyze_threats(system_components: List[str], data_flows: List[str] = None) -> Dict[str, Any]:
    """
    Perform comprehensive threat analysis using STRIDE methodology.

    Args:
        system_components: List of system components (web app, database, API, etc.)
        data_flows: List of data flow descriptions

    Returns:
        Dict containing identified threats organized by STRIDE categories
    """
    if data_flows is None:
        data_flows = []

    threats_by_category = {category.value: [] for category in ThreatCategory}

    # Define common threat vectors for different components
    component_threats = {
        "web_application": [
            ThreatVector(
                name="Cross-Site Scripting (XSS)",
                category=ThreatCategory.TAMPERING,
                description="Malicious scripts injected into web pages",
                likelihood=RiskLevel.HIGH,
                impact=RiskLevel.MEDIUM,
                assets_at_risk=["user_data", "session_tokens"],
                mitigations=["Input validation", "Content Security Policy", "Output encoding"]
            ),
            ThreatVector(
                name="SQL Injection",
                category=ThreatCategory.INFORMATION_DISCLOSURE,
                description="Malicious SQL code injection through user inputs",
                likelihood=RiskLevel.MEDIUM,
                impact=RiskLevel.CRITICAL,
                assets_at_risk=["database", "sensitive_data"],
                mitigations=["Parameterized queries", "Input validation", "Least privilege DB access"]
            ),
            ThreatVector(
                name="Session Hijacking",
                category=ThreatCategory.SPOOFING,
                description="Unauthorized access through stolen session tokens",
                likelihood=RiskLevel.MEDIUM,
                impact=RiskLevel.HIGH,
                assets_at_risk=["user_sessions", "authentication_system"],
                mitigations=["HTTPS only", "Secure cookie flags", "Session timeout"]
            )
        ],
        "api": [
            ThreatVector(
                name="Broken Authentication",
                category=ThreatCategory.ELEVATION_OF_PRIVILEGE,
                description="Weak or bypassed authentication mechanisms",
                likelihood=RiskLevel.HIGH,
                impact=RiskLevel.CRITICAL,
                assets_at_risk=["api_endpoints", "sensitive_operations"],
                mitigations=["Strong authentication", "Rate limiting", "API key management"]
            ),
            ThreatVector(
                name="Data Exposure",
                category=ThreatCategory.INFORMATION_DISCLOSURE,
                description="Excessive data returned in API responses",
                likelihood=RiskLevel.MEDIUM,
                impact=RiskLevel.MEDIUM,
                assets_at_risk=["user_data", "business_logic"],
                mitigations=["Response filtering", "Field-level permissions", "API versioning"]
            )
        ],
        "database": [
            ThreatVector(
                name="Data Breach",
                category=ThreatCategory.INFORMATION_DISCLOSURE,
                description="Unauthorized access to sensitive database information",
                likelihood=RiskLevel.LOW,
                impact=RiskLevel.CRITICAL,
                assets_at_risk=["personal_data", "financial_records", "business_secrets"],
                mitigations=["Encryption at rest", "Access controls", "Database monitoring"]
            ),
            ThreatVector(
                name="Privilege Escalation",
                category=ThreatCategory.ELEVATION_OF_PRIVILEGE,
                description="Unauthorized elevation of database user privileges",
                likelihood=RiskLevel.LOW,
                impact=RiskLevel.HIGH,
                assets_at_risk=["database_integrity", "system_administration"],
                mitigations=["Role-based access", "Regular privilege audits", "Principle of least privilege"]
            )
        ]
    }

    # Analyze threats for each component
    for component in system_components:
        component_key = component.lower().replace(" ", "_")
        if component_key in component_threats:
            for threat in component_threats[component_key]:
                threats_by_category[threat.category.value].append({
                    "name": threat.name,
                    "component": component,
                    "description": threat.description,
                    "likelihood": threat.likelihood.name,
                    "impact": threat.impact.name,
                    "risk_score": threat.likelihood.value * threat.impact.value,
                    "assets_at_risk": threat.assets_at_risk,
                    "mitigations": threat.mitigations
                })

    # Calculate overall risk metrics
    all_threats = []
    for category_threats in threats_by_category.values():
        all_threats.extend(category_threats)

    risk_summary = {
        "total_threats": len(all_threats),
        "critical_risk": len([t for t in all_threats if t["risk_score"] >= 12]),
        "high_risk": len([t for t in all_threats if 8 <= t["risk_score"] < 12]),
        "medium_risk": len([t for t in all_threats if 4 <= t["risk_score"] < 8]),
        "low_risk": len([t for t in all_threats if t["risk_score"] < 4])
    }

    return {
        "threats_by_category": threats_by_category,
        "risk_summary": risk_summary,
        "methodology": "STRIDE (Spoofing, Tampering, Repudiation, Information Disclosure, DoS, Elevation of Privilege)",
        "recommendations": [
            "Prioritize critical and high-risk threats for immediate mitigation",
            "Implement defense-in-depth security strategy",
            "Regular threat model updates as system evolves",
            "Security testing aligned with identified threat vectors"
        ]
    }


async def create_threat_model(project_description: str, architecture: Dict[str, Any] = None) -> Dict[str, Any]:
    """
    Create a comprehensive threat model for a project.

    Args:
        project_description: Description of the project/system
        architecture: Architecture details (components, data flows, trust boundaries)

    Returns:
        Dict containing complete threat model
    """
    if architecture is None:
        architecture = {}

    # Extract system components from description and architecture
    components = architecture.get("components", ["web_application", "api", "database"])
    data_flows = architecture.get("data_flows", [])
    trust_boundaries = architecture.get("trust_boundaries", ["internet", "application", "database"])

    # Perform threat analysis
    threat_analysis = await analyze_threats(components, data_flows)

    # Create threat model structure
    threat_model = {
        "project": {
            "name": architecture.get("name", "Unnamed Project"),
            "description": project_description,
            "scope": architecture.get("scope", "Full application stack"),
            "assumptions": architecture.get("assumptions", [
                "Network traffic may be intercepted",
                "Attackers have internet access",
                "Internal systems may be compromised"
            ])
        },
        "architecture": {
            "components": components,
            "data_flows": data_flows,
            "trust_boundaries": trust_boundaries,
            "sensitive_assets": architecture.get("sensitive_assets", [
                "user_credentials", "personal_data", "business_logic", "system_configuration"
            ])
        },
        "threat_analysis": threat_analysis["threats_by_category"],
        "risk_assessment": threat_analysis["risk_summary"],
        "security_controls": {
            "existing": architecture.get("existing_controls", []),
            "recommended": _get_recommended_controls(threat_analysis["threats_by_category"]),
            "priority_order": _prioritize_controls(threat_analysis["threats_by_category"])
        },
        "validation": {
            "testing_requirements": _generate_testing_requirements(threat_analysis["threats_by_category"]),
            "review_schedule": "Quarterly or after major changes",
            "stakeholders": ["Security Team", "Development Team", "Architecture Team"]
        }
    }

    return threat_model


async def assess_attack_vectors(entry_points: List[str], system_type: str = "web_application") -> Dict[str, Any]:
    """
    Assess potential attack vectors for given entry points.

    Args:
        entry_points: List of system entry points (URLs, APIs, etc.)
        system_type: Type of system being analyzed

    Returns:
        Dict containing attack vector analysis
    """
    attack_vectors = {
        "network_based": [],
        "application_based": [],
        "physical_based": [],
        "social_engineering": []
    }

    # Network-based attacks
    attack_vectors["network_based"] = [
        {
            "name": "Man-in-the-Middle",
            "description": "Interception of network communications",
            "entry_points": [ep for ep in entry_points if "http" in ep.lower()],
            "severity": "high",
            "mitigations": ["HTTPS/TLS", "Certificate pinning", "HSTS headers"]
        },
        {
            "name": "DDoS Attack",
            "description": "Overwhelming system resources",
            "entry_points": entry_points,
            "severity": "medium",
            "mitigations": ["Rate limiting", "CDN protection", "Load balancing"]
        }
    ]

    # Application-based attacks
    attack_vectors["application_based"] = [
        {
            "name": "Input Validation Bypass",
            "description": "Malicious input processing",
            "entry_points": [ep for ep in entry_points if any(x in ep for x in ["/api/", "/form", "?"])],
            "severity": "high",
            "mitigations": ["Input validation", "Sanitization", "Parameterized queries"]
        },
        {
            "name": "Authentication Bypass",
            "description": "Unauthorized access attempts",
            "entry_points": [ep for ep in entry_points if any(x in ep for x in ["/login", "/auth", "/admin"])],
            "severity": "critical",
            "mitigations": ["Multi-factor authentication", "Account lockout", "Strong password policies"]
        }
    ]

    # Social engineering attacks
    attack_vectors["social_engineering"] = [
        {
            "name": "Phishing",
            "description": "Credential harvesting through deception",
            "entry_points": ["email", "social_media", "phone"],
            "severity": "high",
            "mitigations": ["User education", "Email filtering", "Domain verification"]
        }
    ]

    return {
        "attack_vectors": attack_vectors,
        "high_risk_entry_points": _identify_high_risk_entry_points(entry_points),
        "recommendations": [
            "Implement comprehensive input validation",
            "Use secure communication protocols",
            "Regular security awareness training",
            "Continuous monitoring and logging"
        ]
    }


async def evaluate_risk_score(threat_likelihood: str, impact_severity: str) -> Dict[str, Any]:
    """
    Calculate risk score based on likelihood and impact.

    Args:
        threat_likelihood: Likelihood level (low, medium, high, critical)
        impact_severity: Impact level (low, medium, high, critical)

    Returns:
        Dict containing risk score and classification
    """
    likelihood_values = {"low": 1, "medium": 2, "high": 3, "critical": 4}
    impact_values = {"low": 1, "medium": 2, "high": 3, "critical": 4}

    likelihood_score = likelihood_values.get(threat_likelihood.lower(), 2)
    impact_score = impact_values.get(impact_severity.lower(), 2)
    risk_score = likelihood_score * impact_score

    # Risk classification matrix
    if risk_score >= 12:
        risk_level = "Critical"
        priority = "Immediate"
    elif risk_score >= 8:
        risk_level = "High"
        priority = "Within 30 days"
    elif risk_score >= 4:
        risk_level = "Medium"
        priority = "Within 90 days"
    else:
        risk_level = "Low"
        priority = "Next release cycle"

    return {
        "risk_score": risk_score,
        "risk_level": risk_level,
        "priority": priority,
        "likelihood": threat_likelihood,
        "impact": impact_severity,
        "recommendation": f"Address this {risk_level.lower()} risk threat {priority.lower()}"
    }


async def suggest_mitigations(threats: List[Dict[str, Any]]) -> Dict[str, Any]:
    """
    Suggest appropriate mitigations for identified threats.

    Args:
        threats: List of threat objects with categories and descriptions

    Returns:
        Dict containing prioritized mitigation strategies
    """
    mitigation_strategies = {
        "immediate_actions": [],
        "short_term_improvements": [],
        "long_term_investments": [],
        "ongoing_practices": []
    }

    # Common mitigation patterns
    mitigation_map = {
        "xss": {
            "immediate": ["Input validation", "Output encoding"],
            "short_term": ["Content Security Policy", "XSS protection headers"],
            "long_term": ["Security-focused frontend framework"],
            "ongoing": ["Regular security testing", "Code review"]
        },
        "injection": {
            "immediate": ["Parameterized queries", "Input sanitization"],
            "short_term": ["Database access controls", "Query monitoring"],
            "long_term": ["ORM framework adoption", "Database encryption"],
            "ongoing": ["Regular penetration testing", "Code analysis"]
        },
        "authentication": {
            "immediate": ["Strong password requirements", "Account lockout"],
            "short_term": ["Multi-factor authentication", "Session management"],
            "long_term": ["Identity provider integration", "Zero-trust architecture"],
            "ongoing": ["Access review", "Privilege auditing"]
        }
    }

    # Analyze threats and suggest mitigations
    threat_categories = set()
    for threat in threats:
        threat_name = threat.get("name", "").lower()
        if "xss" in threat_name or "script" in threat_name:
            threat_categories.add("xss")
        elif "injection" in threat_name or "sql" in threat_name:
            threat_categories.add("injection")
        elif "auth" in threat_name or "login" in threat_name:
            threat_categories.add("authentication")

    # Compile mitigation recommendations
    for category in threat_categories:
        if category in mitigation_map:
            mitigations = mitigation_map[category]
            mitigation_strategies["immediate_actions"].extend(mitigations["immediate"])
            mitigation_strategies["short_term_improvements"].extend(mitigations["short_term"])
            mitigation_strategies["long_term_investments"].extend(mitigations["long_term"])
            mitigation_strategies["ongoing_practices"].extend(mitigations["ongoing"])

    # Remove duplicates and prioritize
    for key in mitigation_strategies:
        mitigation_strategies[key] = list(set(mitigation_strategies[key]))

    return {
        "mitigation_strategies": mitigation_strategies,
        "implementation_timeline": {
            "immediate": "0-7 days",
            "short_term": "1-3 months",
            "long_term": "3-12 months",
            "ongoing": "Continuous"
        },
        "success_metrics": [
            "Reduction in vulnerability count",
            "Faster incident response time",
            "Improved security test coverage",
            "Enhanced monitoring capabilities"
        ]
    }


async def document_security_requirements(threats: List[Dict[str, Any]], compliance_frameworks: List[str] = None) -> Dict[str, Any]:
    """
    Generate security requirements documentation based on threat analysis.

    Args:
        threats: List of identified threats
        compliance_frameworks: List of compliance frameworks to consider

    Returns:
        Dict containing security requirements documentation
    """
    if compliance_frameworks is None:
        compliance_frameworks = ["OWASP", "NIST", "ISO27001"]

    security_requirements = {
        "authentication": [],
        "authorization": [],
        "data_protection": [],
        "communication_security": [],
        "logging_monitoring": [],
        "incident_response": []
    }

    # Generate requirements based on threats
    for threat in threats:
        threat_category = threat.get("category", "").lower()

        if "spoofing" in threat_category or "auth" in threat.get("name", "").lower():
            security_requirements["authentication"].append(
                "Implement strong authentication mechanisms with multi-factor authentication"
            )

        if "tampering" in threat_category or "injection" in threat.get("name", "").lower():
            security_requirements["data_protection"].append(
                "Validate and sanitize all input data to prevent injection attacks"
            )

        if "information_disclosure" in threat_category:
            security_requirements["data_protection"].append(
                "Encrypt sensitive data both at rest and in transit"
            )

        if "denial_of_service" in threat_category:
            security_requirements["communication_security"].append(
                "Implement rate limiting and DDoS protection mechanisms"
            )

    # Add framework-specific requirements
    framework_requirements = {
        "OWASP": [
            "Follow OWASP Top 10 mitigation guidelines",
            "Implement secure coding practices per OWASP standards",
            "Use OWASP testing guide for security validation"
        ],
        "NIST": [
            "Implement NIST Cybersecurity Framework controls",
            "Follow NIST guidelines for access control",
            "Use NIST risk management processes"
        ],
        "ISO27001": [
            "Establish information security management system",
            "Implement risk assessment processes",
            "Maintain security incident response procedures"
        ]
    }

    compliance_mapping = {}
    for framework in compliance_frameworks:
        if framework in framework_requirements:
            compliance_mapping[framework] = framework_requirements[framework]

    return {
        "security_requirements": security_requirements,
        "compliance_mapping": compliance_mapping,
        "verification_methods": {
            "testing": ["Penetration testing", "Vulnerability scanning", "Security code review"],
            "monitoring": ["Security event logging", "Anomaly detection", "Compliance auditing"],
            "documentation": ["Security architecture review", "Threat model validation", "Incident playbooks"]
        },
        "maintenance": {
            "review_frequency": "Quarterly",
            "update_triggers": ["New threats identified", "Architecture changes", "Compliance updates"],
            "stakeholders": ["Security team", "Development team", "Compliance team"]
        }
    }


def _get_recommended_controls(threats_by_category: Dict[str, List]) -> List[str]:
    """Generate recommended security controls based on threat categories."""
    controls = set()

    for category, category_threats in threats_by_category.items():
        if category_threats:  # If there are threats in this category
            if category == "Spoofing":
                controls.update(["Multi-factor authentication", "Identity verification"])
            elif category == "Tampering":
                controls.update(["Input validation", "Data integrity checks"])
            elif category == "Information Disclosure":
                controls.update(["Data encryption", "Access controls"])
            elif category == "Denial of Service":
                controls.update(["Rate limiting", "Resource monitoring"])
            elif category == "Elevation of Privilege":
                controls.update(["Principle of least privilege", "Role-based access"])

    return list(controls)


def _prioritize_controls(threats_by_category: Dict[str, List]) -> List[str]:
    """Prioritize security controls based on threat severity."""
    high_priority = []
    medium_priority = []

    for category, category_threats in threats_by_category.items():
        for threat in category_threats:
            if threat.get("risk_score", 0) >= 8:
                high_priority.extend(threat.get("mitigations", []))
            else:
                medium_priority.extend(threat.get("mitigations", []))

    return list(set(high_priority)) + list(set(medium_priority))


def _generate_testing_requirements(threats_by_category: Dict[str, List]) -> List[str]:
    """Generate security testing requirements based on identified threats."""
    testing_requirements = []

    for category, category_threats in threats_by_category.items():
        if category_threats:
            if category == "Tampering":
                testing_requirements.append("Input validation testing")
            elif category == "Information Disclosure":
                testing_requirements.append("Data leakage testing")
            elif category == "Spoofing":
                testing_requirements.append("Authentication bypass testing")

    return list(set(testing_requirements))


def _identify_high_risk_entry_points(entry_points: List[str]) -> List[str]:
    """Identify high-risk entry points based on common patterns."""
    high_risk_patterns = ["/admin", "/api", "/login", "/upload", "/search"]
    high_risk_points = []

    for entry_point in entry_points:
        if any(pattern in entry_point.lower() for pattern in high_risk_patterns):
            high_risk_points.append(entry_point)

    return high_risk_points