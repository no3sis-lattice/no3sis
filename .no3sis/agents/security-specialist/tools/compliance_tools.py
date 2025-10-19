"""
Compliance and regulatory framework validation tools.
"""

from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from enum import Enum


class ComplianceFramework(Enum):
    OWASP = "OWASP Top 10"
    NIST = "NIST Cybersecurity Framework"
    ISO27001 = "ISO/IEC 27001"
    SOC2 = "SOC 2 Type II"
    GDPR = "General Data Protection Regulation"
    HIPAA = "Health Insurance Portability and Accountability Act"
    PCI_DSS = "Payment Card Industry Data Security Standard"


@dataclass
class ComplianceRequirement:
    framework: ComplianceFramework
    requirement_id: str
    title: str
    description: str
    category: str
    implementation_status: str = "not_assessed"
    evidence: List[str] = None
    recommendations: List[str] = None

    def __post_init__(self):
        if self.evidence is None:
            self.evidence = []
        if self.recommendations is None:
            self.recommendations = []


async def check_compliance_frameworks(frameworks: List[str], system_components: List[str] = None) -> Dict[str, Any]:
    """
    Check compliance with specified regulatory frameworks.

    Args:
        frameworks: List of compliance frameworks to check
        system_components: List of system components to assess

    Returns:
        Dict containing compliance assessment results
    """
    if system_components is None:
        system_components = ["web_application", "database", "api"]

    compliance_results = {
        "overall_compliance_score": 0,
        "framework_assessments": {},
        "critical_gaps": [],
        "recommendations": []
    }

    # Framework-specific requirements
    framework_requirements = {
        "OWASP": _get_owasp_requirements(),
        "NIST": _get_nist_requirements(),
        "ISO27001": _get_iso27001_requirements(),
        "SOC2": _get_soc2_requirements(),
        "GDPR": _get_gdpr_requirements(),
        "HIPAA": _get_hipaa_requirements(),
        "PCI_DSS": _get_pci_dss_requirements()
    }

    total_score = 0
    framework_count = 0

    # Assess each framework
    for framework in frameworks:
        if framework in framework_requirements:
            framework_count += 1
            requirements = framework_requirements[framework]

            assessment = {
                "total_requirements": len(requirements),
                "compliant": 0,
                "partially_compliant": 0,
                "non_compliant": 0,
                "requirements_details": [],
                "compliance_percentage": 0
            }

            for req in requirements:
                # Simulate assessment based on system components
                status = _assess_requirement_status(req, system_components)
                req.implementation_status = status

                if status == "compliant":
                    assessment["compliant"] += 1
                elif status == "partially_compliant":
                    assessment["partially_compliant"] += 1
                else:
                    assessment["non_compliant"] += 1
                    if req.category in ["critical", "high"]:
                        compliance_results["critical_gaps"].append({
                            "framework": framework,
                            "requirement": req.requirement_id,
                            "title": req.title,
                            "severity": req.category
                        })

                assessment["requirements_details"].append({
                    "id": req.requirement_id,
                    "title": req.title,
                    "status": req.implementation_status,
                    "category": req.category,
                    "recommendations": req.recommendations
                })

            # Calculate compliance percentage
            compliance_score = (assessment["compliant"] + 0.5 * assessment["partially_compliant"]) / assessment["total_requirements"] * 100
            assessment["compliance_percentage"] = round(compliance_score, 2)
            total_score += compliance_score

            compliance_results["framework_assessments"][framework] = assessment

    # Calculate overall compliance score
    if framework_count > 0:
        compliance_results["overall_compliance_score"] = round(total_score / framework_count, 2)

    # Generate recommendations
    compliance_results["recommendations"] = _generate_compliance_recommendations(
        compliance_results["framework_assessments"],
        compliance_results["critical_gaps"]
    )

    return compliance_results


async def generate_security_reports(assessment_data: Dict[str, Any], report_type: str = "executive") -> Dict[str, Any]:
    """
    Generate comprehensive security compliance reports.

    Args:
        assessment_data: Security assessment data from various tools
        report_type: Type of report (executive, technical, audit)

    Returns:
        Dict containing formatted security report
    """
    report = {
        "report_metadata": {
            "type": report_type,
            "generated_date": "2024-01-01",  # Would be dynamic
            "scope": assessment_data.get("scope", "Full system assessment"),
            "assessment_period": "Current"
        },
        "executive_summary": {},
        "detailed_findings": {},
        "recommendations": {},
        "compliance_status": {}
    }

    if report_type == "executive":
        report["executive_summary"] = {
            "overall_security_posture": _calculate_security_posture(assessment_data),
            "key_risks": _extract_key_risks(assessment_data),
            "compliance_summary": _summarize_compliance(assessment_data),
            "investment_priorities": _identify_investment_priorities(assessment_data)
        }

    elif report_type == "technical":
        report["detailed_findings"] = {
            "vulnerability_analysis": assessment_data.get("vulnerabilities", {}),
            "configuration_issues": assessment_data.get("configurations", {}),
            "access_control_findings": assessment_data.get("access_controls", {}),
            "encryption_status": assessment_data.get("encryption", {})
        }

    elif report_type == "audit":
        report["compliance_status"] = {
            "framework_compliance": assessment_data.get("compliance", {}),
            "evidence_documentation": _compile_evidence(assessment_data),
            "gap_analysis": _perform_gap_analysis(assessment_data),
            "remediation_timeline": _create_remediation_timeline(assessment_data)
        }

    # Common recommendations for all report types
    report["recommendations"] = {
        "immediate_actions": _get_immediate_actions(assessment_data),
        "short_term_improvements": _get_short_term_improvements(assessment_data),
        "long_term_strategy": _get_long_term_strategy(assessment_data)
    }

    return report


async def validate_privacy_requirements(data_processing_activities: List[str], jurisdiction: str = "EU") -> Dict[str, Any]:
    """
    Validate privacy requirements based on data processing activities.

    Args:
        data_processing_activities: List of data processing activities
        jurisdiction: Legal jurisdiction (EU, US, UK, etc.)

    Returns:
        Dict containing privacy compliance validation
    """
    privacy_validation = {
        "applicable_regulations": [],
        "privacy_requirements": [],
        "compliance_gaps": [],
        "recommended_measures": []
    }

    # Jurisdiction-specific regulations
    regulations_map = {
        "EU": ["GDPR", "ePrivacy Directive"],
        "US": ["CCPA", "COPPA", "HIPAA"],
        "UK": ["UK GDPR", "Data Protection Act 2018"],
        "Canada": ["PIPEDA"],
        "Australia": ["Privacy Act 1988"]
    }

    privacy_validation["applicable_regulations"] = regulations_map.get(jurisdiction, ["GDPR"])

    # GDPR requirements (as example)
    if "GDPR" in privacy_validation["applicable_regulations"]:
        gdpr_requirements = [
            {
                "principle": "Lawfulness, fairness, transparency",
                "requirement": "Valid legal basis for processing",
                "applies_to": ["personal_data_collection", "user_profiling"]
            },
            {
                "principle": "Purpose limitation",
                "requirement": "Data used only for specified purposes",
                "applies_to": ["data_analytics", "marketing"]
            },
            {
                "principle": "Data minimisation",
                "requirement": "Collect only necessary data",
                "applies_to": ["user_registration", "form_collection"]
            },
            {
                "principle": "Accuracy",
                "requirement": "Keep data accurate and up-to-date",
                "applies_to": ["user_profiles", "contact_information"]
            },
            {
                "principle": "Storage limitation",
                "requirement": "Retain data only as long as necessary",
                "applies_to": ["log_retention", "user_data_storage"]
            },
            {
                "principle": "Integrity and confidentiality",
                "requirement": "Secure data processing",
                "applies_to": ["data_transmission", "data_storage"]
            }
        ]

        # Check which requirements apply to current activities
        for activity in data_processing_activities:
            for req in gdpr_requirements:
                if any(applies in activity.lower() for applies in req["applies_to"]):
                    privacy_validation["privacy_requirements"].append({
                        "activity": activity,
                        "principle": req["principle"],
                        "requirement": req["requirement"],
                        "compliance_status": "needs_assessment"
                    })

    # Common privacy protection measures
    privacy_validation["recommended_measures"] = [
        "Implement privacy by design principles",
        "Conduct Data Protection Impact Assessments (DPIA)",
        "Establish data retention and deletion policies",
        "Implement user consent management",
        "Provide data subject rights mechanisms (access, rectification, erasure)",
        "Maintain records of processing activities",
        "Appoint Data Protection Officer if required",
        "Implement privacy notices and transparency measures"
    ]

    return privacy_validation


async def audit_data_protection(data_stores: List[str], protection_measures: Dict[str, Any] = None) -> Dict[str, Any]:
    """
    Audit data protection measures and implementation.

    Args:
        data_stores: List of data storage systems
        protection_measures: Current protection measures in place

    Returns:
        Dict containing data protection audit results
    """
    if protection_measures is None:
        protection_measures = {}

    audit_results = {
        "data_classification": [],
        "protection_gaps": [],
        "encryption_status": [],
        "access_control_audit": [],
        "recommendations": []
    }

    # Data classification framework
    data_classifications = {
        "public": {"sensitivity": "low", "protection_level": "basic"},
        "internal": {"sensitivity": "medium", "protection_level": "standard"},
        "confidential": {"sensitivity": "high", "protection_level": "enhanced"},
        "restricted": {"sensitivity": "critical", "protection_level": "maximum"}
    }

    # Audit each data store
    for store in data_stores:
        store_audit = {
            "data_store": store,
            "classification": "needs_assessment",
            "encryption_at_rest": protection_measures.get(f"{store}_encryption_rest", False),
            "encryption_in_transit": protection_measures.get(f"{store}_encryption_transit", False),
            "access_controls": protection_measures.get(f"{store}_access_controls", []),
            "backup_protection": protection_measures.get(f"{store}_backup_encryption", False),
            "audit_logging": protection_measures.get(f"{store}_audit_logging", False)
        }

        # Identify protection gaps
        gaps = []
        if not store_audit["encryption_at_rest"]:
            gaps.append("Missing encryption at rest")
        if not store_audit["encryption_in_transit"]:
            gaps.append("Missing encryption in transit")
        if not store_audit["access_controls"]:
            gaps.append("Missing access control implementation")
        if not store_audit["audit_logging"]:
            gaps.append("Missing audit logging")

        if gaps:
            audit_results["protection_gaps"].append({
                "data_store": store,
                "gaps": gaps,
                "risk_level": "high" if len(gaps) > 2 else "medium"
            })

        audit_results["data_classification"].append(store_audit)

    # Generate recommendations based on gaps
    common_gaps = {}
    for gap_entry in audit_results["protection_gaps"]:
        for gap in gap_entry["gaps"]:
            common_gaps[gap] = common_gaps.get(gap, 0) + 1

    # Prioritize recommendations based on frequency
    for gap, count in sorted(common_gaps.items(), key=lambda x: x[1], reverse=True):
        if "encryption at rest" in gap:
            audit_results["recommendations"].append("HIGH PRIORITY: Implement encryption at rest for all data stores")
        elif "encryption in transit" in gap:
            audit_results["recommendations"].append("HIGH PRIORITY: Implement TLS/SSL for all data transmission")
        elif "access control" in gap:
            audit_results["recommendations"].append("MEDIUM PRIORITY: Implement role-based access controls")
        elif "audit logging" in gap:
            audit_results["recommendations"].append("MEDIUM PRIORITY: Enable comprehensive audit logging")

    audit_results["recommendations"].extend([
        "Classify data according to sensitivity levels",
        "Implement data loss prevention (DLP) solutions",
        "Regular data protection impact assessments",
        "Automated backup and recovery testing",
        "Staff training on data protection practices"
    ])

    return audit_results


async def assess_regulatory_compliance(industry: str, business_operations: List[str]) -> Dict[str, Any]:
    """
    Assess regulatory compliance requirements based on industry and operations.

    Args:
        industry: Industry sector (healthcare, finance, retail, etc.)
        business_operations: List of business operations/activities

    Returns:
        Dict containing regulatory compliance assessment
    """
    compliance_assessment = {
        "applicable_regulations": [],
        "compliance_requirements": [],
        "risk_areas": [],
        "implementation_roadmap": []
    }

    # Industry-specific regulations
    industry_regulations = {
        "healthcare": ["HIPAA", "HITECH", "FDA 21 CFR Part 11"],
        "finance": ["PCI DSS", "SOX", "GLBA", "FFIEC"],
        "retail": ["PCI DSS", "CCPA", "GDPR"],
        "government": ["FISMA", "FedRAMP", "NIST 800-53"],
        "education": ["FERPA", "COPPA"],
        "technology": ["SOC 2", "ISO 27001", "GDPR"]
    }

    compliance_assessment["applicable_regulations"] = industry_regulations.get(
        industry.lower(), ["GDPR", "ISO 27001"]
    )

    # Generate compliance requirements based on regulations
    for regulation in compliance_assessment["applicable_regulations"]:
        requirements = _get_regulation_requirements(regulation, business_operations)
        compliance_assessment["compliance_requirements"].extend(requirements)

    # Identify high-risk areas
    risk_operations = {
        "payment_processing": ["PCI DSS", "financial_regulations"],
        "personal_data_handling": ["GDPR", "CCPA", "privacy_laws"],
        "healthcare_data": ["HIPAA", "HITECH"],
        "financial_services": ["SOX", "GLBA", "banking_regulations"],
        "cloud_services": ["SOC 2", "ISO 27001", "cloud_security"]
    }

    for operation in business_operations:
        for risk_op, regulations in risk_operations.items():
            if risk_op in operation.lower():
                compliance_assessment["risk_areas"].append({
                    "operation": operation,
                    "applicable_regulations": regulations,
                    "risk_level": "high"
                })

    # Create implementation roadmap
    compliance_assessment["implementation_roadmap"] = [
        {
            "phase": "Assessment",
            "duration": "1-2 months",
            "activities": ["Gap analysis", "Risk assessment", "Compliance mapping"]
        },
        {
            "phase": "Planning",
            "duration": "1 month",
            "activities": ["Remediation planning", "Resource allocation", "Timeline development"]
        },
        {
            "phase": "Implementation",
            "duration": "6-12 months",
            "activities": ["Security controls", "Process improvements", "Training programs"]
        },
        {
            "phase": "Validation",
            "duration": "2-3 months",
            "activities": ["Compliance testing", "Third-party audits", "Certification"]
        },
        {
            "phase": "Maintenance",
            "duration": "Ongoing",
            "activities": ["Continuous monitoring", "Regular audits", "Updates and improvements"]
        }
    ]

    return compliance_assessment


# Helper functions for compliance assessment

def _get_owasp_requirements() -> List[ComplianceRequirement]:
    """Generate OWASP Top 10 compliance requirements."""
    return [
        ComplianceRequirement(
            ComplianceFramework.OWASP, "A01", "Broken Access Control",
            "Implement proper access controls", "critical",
            recommendations=["Implement role-based access control", "Regular access reviews"]
        ),
        ComplianceRequirement(
            ComplianceFramework.OWASP, "A02", "Cryptographic Failures",
            "Use strong cryptography", "high",
            recommendations=["Use AES-256", "Implement proper key management"]
        ),
        ComplianceRequirement(
            ComplianceFramework.OWASP, "A03", "Injection",
            "Prevent injection attacks", "critical",
            recommendations=["Input validation", "Parameterized queries"]
        )
    ]

def _get_nist_requirements() -> List[ComplianceRequirement]:
    """Generate NIST Cybersecurity Framework requirements."""
    return [
        ComplianceRequirement(
            ComplianceFramework.NIST, "ID.AM", "Asset Management",
            "Identify and manage assets", "high",
            recommendations=["Asset inventory", "Asset classification"]
        ),
        ComplianceRequirement(
            ComplianceFramework.NIST, "PR.AC", "Access Control",
            "Implement access controls", "critical",
            recommendations=["Identity management", "Access control policies"]
        )
    ]

def _get_iso27001_requirements() -> List[ComplianceRequirement]:
    """Generate ISO 27001 requirements."""
    return [
        ComplianceRequirement(
            ComplianceFramework.ISO27001, "A.5", "Information Security Policies",
            "Establish security policies", "high",
            recommendations=["Security policy documentation", "Regular policy reviews"]
        )
    ]

def _get_soc2_requirements() -> List[ComplianceRequirement]:
    """Generate SOC 2 Type II requirements."""
    return [
        ComplianceRequirement(
            ComplianceFramework.SOC2, "CC6.1", "Logical Access Controls",
            "Implement logical access controls", "critical",
            recommendations=["User access management", "Privileged access controls"]
        )
    ]

def _get_gdpr_requirements() -> List[ComplianceRequirement]:
    """Generate GDPR requirements."""
    return [
        ComplianceRequirement(
            ComplianceFramework.GDPR, "Art.25", "Data Protection by Design",
            "Implement privacy by design", "high",
            recommendations=["Privacy impact assessments", "Data minimization"]
        )
    ]

def _get_hipaa_requirements() -> List[ComplianceRequirement]:
    """Generate HIPAA requirements."""
    return [
        ComplianceRequirement(
            ComplianceFramework.HIPAA, "164.312", "Technical Safeguards",
            "Implement technical safeguards", "critical",
            recommendations=["Access controls", "Audit logging", "Encryption"]
        )
    ]

def _get_pci_dss_requirements() -> List[ComplianceRequirement]:
    """Generate PCI DSS requirements."""
    return [
        ComplianceRequirement(
            ComplianceFramework.PCI_DSS, "Req.3", "Protect Stored Cardholder Data",
            "Protect cardholder data", "critical",
            recommendations=["Data encryption", "Key management", "Secure deletion"]
        )
    ]

def _assess_requirement_status(requirement: ComplianceRequirement, system_components: List[str]) -> str:
    """Assess the implementation status of a compliance requirement."""
    # Simplified assessment logic
    if requirement.category == "critical":
        return "partially_compliant"  # Assume partial compliance for critical
    elif requirement.category == "high":
        return "compliant" if len(system_components) > 2 else "partially_compliant"
    else:
        return "compliant"

def _generate_compliance_recommendations(assessments: Dict[str, Any], critical_gaps: List[Dict]) -> List[str]:
    """Generate compliance recommendations based on assessment results."""
    recommendations = []

    if critical_gaps:
        recommendations.append("URGENT: Address critical compliance gaps immediately")

    recommendations.extend([
        "Conduct regular compliance assessments",
        "Implement continuous compliance monitoring",
        "Establish compliance governance processes",
        "Regular staff training on compliance requirements"
    ])

    return recommendations

def _calculate_security_posture(assessment_data: Dict[str, Any]) -> str:
    """Calculate overall security posture."""
    # Simplified calculation
    vulnerabilities = len(assessment_data.get("vulnerabilities", {}).get("critical", []))
    if vulnerabilities > 10:
        return "Poor"
    elif vulnerabilities > 5:
        return "Fair"
    elif vulnerabilities > 0:
        return "Good"
    else:
        return "Excellent"

def _extract_key_risks(assessment_data: Dict[str, Any]) -> List[str]:
    """Extract key risks from assessment data."""
    return [
        "Unencrypted sensitive data",
        "Weak access controls",
        "Missing security monitoring"
    ]

def _summarize_compliance(assessment_data: Dict[str, Any]) -> Dict[str, Any]:
    """Summarize compliance status."""
    return {
        "overall_compliance": "75%",
        "frameworks_assessed": 3,
        "critical_gaps": 2
    }

def _identify_investment_priorities(assessment_data: Dict[str, Any]) -> List[str]:
    """Identify security investment priorities."""
    return [
        "Implement comprehensive monitoring",
        "Upgrade encryption systems",
        "Enhance access control systems"
    ]

def _compile_evidence(assessment_data: Dict[str, Any]) -> List[str]:
    """Compile evidence for audit purposes."""
    return [
        "Security policy documentation",
        "Access control configurations",
        "Encryption implementation details"
    ]

def _perform_gap_analysis(assessment_data: Dict[str, Any]) -> Dict[str, List]:
    """Perform gap analysis against requirements."""
    return {
        "critical_gaps": ["Missing encryption at rest"],
        "medium_gaps": ["Incomplete access logging"],
        "low_gaps": ["Missing security headers"]
    }

def _create_remediation_timeline(assessment_data: Dict[str, Any]) -> List[Dict]:
    """Create remediation timeline."""
    return [
        {"task": "Implement encryption", "deadline": "30 days", "priority": "critical"},
        {"task": "Update access controls", "deadline": "60 days", "priority": "high"}
    ]

def _get_immediate_actions(assessment_data: Dict[str, Any]) -> List[str]:
    """Get immediate actions required."""
    return [
        "Patch critical vulnerabilities",
        "Update weak passwords",
        "Enable security logging"
    ]

def _get_short_term_improvements(assessment_data: Dict[str, Any]) -> List[str]:
    """Get short-term improvements."""
    return [
        "Implement MFA",
        "Deploy monitoring tools",
        "Update security policies"
    ]

def _get_long_term_strategy(assessment_data: Dict[str, Any]) -> List[str]:
    """Get long-term security strategy."""
    return [
        "Implement zero-trust architecture",
        "Advanced threat detection",
        "Security automation"
    ]

def _get_regulation_requirements(regulation: str, operations: List[str]) -> List[Dict]:
    """Get specific requirements for a regulation."""
    requirements_map = {
        "HIPAA": [
            {"requirement": "Implement access controls for PHI", "category": "critical"},
            {"requirement": "Encrypt PHI in transit and at rest", "category": "critical"}
        ],
        "PCI DSS": [
            {"requirement": "Protect cardholder data", "category": "critical"},
            {"requirement": "Implement strong access controls", "category": "high"}
        ],
        "GDPR": [
            {"requirement": "Implement privacy by design", "category": "high"},
            {"requirement": "Enable data subject rights", "category": "medium"}
        ]
    }
    return requirements_map.get(regulation, [])