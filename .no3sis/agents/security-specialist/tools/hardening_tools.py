"""
Security hardening and configuration validation tools.
"""

import json
import os
import re
from pathlib import Path
from typing import Dict, List, Any, Optional


async def suggest_hardening(system_type: str = "web_application", current_config: Dict[str, Any] = None) -> Dict[str, Any]:
    """
    Suggest security hardening measures based on system type and current configuration.

    Args:
        system_type: Type of system (web_application, api, database, etc.)
        current_config: Current system configuration

    Returns:
        Dict containing hardening recommendations
    """
    if current_config is None:
        current_config = {}

    hardening_recommendations = {
        "critical": [],
        "high": [],
        "medium": [],
        "low": [],
        "implementation_guides": {}
    }

    # System-specific hardening recommendations
    system_hardening = {
        "web_application": {
            "critical": [
                "Enable HTTPS with strong TLS configuration (TLS 1.2+)",
                "Implement Content Security Policy (CSP)",
                "Remove or secure default accounts and configurations"
            ],
            "high": [
                "Configure security headers (HSTS, X-Frame-Options, X-Content-Type-Options)",
                "Implement input validation and output encoding",
                "Enable Web Application Firewall (WAF)"
            ],
            "medium": [
                "Configure session management (secure flags, timeout)",
                "Implement rate limiting",
                "Regular security updates and patching"
            ],
            "low": [
                "Remove server version headers",
                "Configure custom error pages",
                "Implement logging and monitoring"
            ]
        },
        "api": {
            "critical": [
                "Implement strong API authentication (OAuth 2.0, JWT)",
                "Use HTTPS for all API endpoints",
                "Validate and sanitize all API inputs"
            ],
            "high": [
                "Implement rate limiting and throttling",
                "Use API versioning and deprecation policies",
                "Configure CORS properly"
            ],
            "medium": [
                "Implement API logging and monitoring",
                "Use input/output schemas validation",
                "Configure proper HTTP status codes"
            ]
        },
        "database": {
            "critical": [
                "Enable database encryption at rest",
                "Use strong authentication and access controls",
                "Implement network segmentation"
            ],
            "high": [
                "Enable database audit logging",
                "Use principle of least privilege for accounts",
                "Regular security updates and patches"
            ],
            "medium": [
                "Configure connection encryption (TLS/SSL)",
                "Implement backup encryption",
                "Set up monitoring and alerting"
            ]
        }
    }

    # Get recommendations for the system type
    if system_type in system_hardening:
        recommendations = system_hardening[system_type]
        hardening_recommendations.update(recommendations)

    # Add implementation guides
    hardening_recommendations["implementation_guides"] = {
        "tls_configuration": {
            "description": "Configure strong TLS/SSL settings",
            "steps": [
                "Use TLS 1.2 or higher",
                "Disable weak cipher suites",
                "Use strong key exchange algorithms",
                "Implement HSTS headers"
            ]
        },
        "csp_implementation": {
            "description": "Implement Content Security Policy",
            "steps": [
                "Start with a restrictive policy",
                "Use nonce or hash for inline scripts",
                "Gradually relax policy based on requirements",
                "Monitor CSP violations"
            ]
        },
        "authentication_hardening": {
            "description": "Strengthen authentication mechanisms",
            "steps": [
                "Implement multi-factor authentication",
                "Use strong password policies",
                "Enable account lockout policies",
                "Implement session management"
            ]
        }
    }

    return hardening_recommendations


async def validate_configuration(config_files: List[str], config_type: str = "web_server") -> Dict[str, Any]:
    """
    Validate security configuration for various system components.

    Args:
        config_files: List of configuration file paths
        config_type: Type of configuration (web_server, database, application)

    Returns:
        Dict containing validation results and recommendations
    """
    validation_results = {
        "secure_configurations": [],
        "insecure_configurations": [],
        "missing_configurations": [],
        "recommendations": []
    }

    # Security configuration patterns for different types
    security_patterns = {
        "web_server": {
            "secure": [
                r"ssl_protocols.*TLSv1\.[23]",
                r"add_header.*Strict-Transport-Security",
                r"add_header.*X-Frame-Options.*DENY",
                r"server_tokens\s+off"
            ],
            "insecure": [
                r"ssl_protocols.*SSLv|TLSv1\s",
                r"server_tokens\s+on",
                r"autoindex\s+on"
            ],
            "required": [
                "SSL/TLS configuration",
                "Security headers",
                "Server signature hiding"
            ]
        },
        "database": {
            "secure": [
                r"ssl\s*=\s*on",
                r"log_statement\s*=\s*'all'",
                r"password_encryption\s*=\s*on"
            ],
            "insecure": [
                r"trust.*authentication",
                r"ssl\s*=\s*off",
                r"log_min_messages\s*=\s*panic"
            ],
            "required": [
                "SSL encryption",
                "Authentication configuration",
                "Audit logging"
            ]
        }
    }

    # Validate each configuration file
    for config_file in config_files:
        config_path = Path(config_file)
        if not config_path.exists():
            validation_results["missing_configurations"].append({
                "file": config_file,
                "message": "Configuration file not found"
            })
            continue

        try:
            content = config_path.read_text()
            patterns = security_patterns.get(config_type, security_patterns["web_server"])

            # Check for secure configurations
            for pattern in patterns["secure"]:
                if re.search(pattern, content, re.IGNORECASE):
                    validation_results["secure_configurations"].append({
                        "file": config_file,
                        "pattern": pattern,
                        "status": "secure"
                    })

            # Check for insecure configurations
            for pattern in patterns["insecure"]:
                if re.search(pattern, content, re.IGNORECASE):
                    validation_results["insecure_configurations"].append({
                        "file": config_file,
                        "pattern": pattern,
                        "status": "insecure",
                        "severity": "high"
                    })

        except Exception as e:
            validation_results["missing_configurations"].append({
                "file": config_file,
                "error": str(e)
            })

    # Generate recommendations
    if validation_results["insecure_configurations"]:
        validation_results["recommendations"].append("Address insecure configurations immediately")

    validation_results["recommendations"].extend([
        "Regular configuration audits",
        "Use configuration management tools",
        "Implement configuration baselines",
        "Monitor configuration drift"
    ])

    return validation_results


async def audit_access_controls(target_path: str = ".", access_type: str = "file_system") -> Dict[str, Any]:
    """
    Audit access controls and permissions.

    Args:
        target_path: Path to audit
        access_type: Type of access control (file_system, database, application)

    Returns:
        Dict containing access control audit results
    """
    audit_results = {
        "excessive_permissions": [],
        "missing_permissions": [],
        "privilege_violations": [],
        "recommendations": []
    }

    if access_type == "file_system":
        # Audit file system permissions
        sensitive_files = [
            ".env", ".config", "config.json", "secrets.yml",
            "private.key", "certificate.crt", "database.db"
        ]

        try:
            for root, dirs, files in os.walk(target_path):
                for file in files:
                    file_path = Path(root) / file
                    if file_path.exists():
                        stat_info = file_path.stat()
                        mode = stat_info.st_mode

                        # Check sensitive files
                        if file in sensitive_files:
                            # Should not be world-readable
                            if mode & 0o044:  # World or group readable
                                audit_results["excessive_permissions"].append({
                                    "path": str(file_path),
                                    "issue": "Sensitive file is world/group readable",
                                    "current_permissions": oct(mode)[-3:],
                                    "recommended_permissions": "600",
                                    "severity": "high"
                                })

                        # Check executable files
                        if mode & 0o111:  # Executable
                            if file.endswith(('.config', '.json', '.yml', '.yaml')):
                                audit_results["privilege_violations"].append({
                                    "path": str(file_path),
                                    "issue": "Configuration file should not be executable",
                                    "severity": "medium"
                                })

        except Exception as e:
            audit_results["error"] = str(e)

    # Add general recommendations
    audit_results["recommendations"] = [
        "Follow principle of least privilege",
        "Regular access control reviews",
        "Use proper file permissions (600 for secrets, 644 for configs)",
        "Implement role-based access control where applicable",
        "Monitor and log access control changes"
    ]

    return audit_results


async def check_encryption(target_path: str = ".", check_type: str = "data_at_rest") -> Dict[str, Any]:
    """
    Check encryption implementation and configuration.

    Args:
        target_path: Path to check
        check_type: Type of encryption check (data_at_rest, data_in_transit, key_management)

    Returns:
        Dict containing encryption analysis results
    """
    encryption_results = {
        "encrypted_files": [],
        "unencrypted_sensitive_files": [],
        "weak_encryption": [],
        "encryption_recommendations": []
    }

    # Patterns for identifying sensitive files that should be encrypted
    sensitive_patterns = [
        r".*\.db$", r".*\.sqlite$", r".*\.sql$",  # Database files
        r".*backup.*", r".*dump.*",  # Backup files
        r".*\.key$", r".*\.pem$", r".*\.p12$",  # Key files
        r".*secret.*", r".*credential.*"  # Secret files
    ]

    # Patterns for weak encryption
    weak_crypto_patterns = [
        r"MD5|md5",
        r"SHA1(?!256|384|512)",
        r"DES(?!ede)",
        r"RC4",
        r"3DES"
    ]

    try:
        for root, dirs, files in os.walk(target_path):
            dirs[:] = [d for d in dirs if d not in ['.git', 'node_modules', '__pycache__']]

            for file in files:
                file_path = Path(root) / file

                # Check if file matches sensitive patterns
                is_sensitive = any(re.match(pattern, file, re.IGNORECASE) for pattern in sensitive_patterns)

                if is_sensitive:
                    # Simple check - if file is not binary, it's likely unencrypted
                    try:
                        with open(file_path, 'rb') as f:
                            chunk = f.read(1024)
                            # If mostly printable ASCII, likely unencrypted
                            if sum(1 for byte in chunk if 32 <= byte <= 126) > len(chunk) * 0.8:
                                encryption_results["unencrypted_sensitive_files"].append({
                                    "file": str(file_path),
                                    "type": "sensitive_data",
                                    "recommendation": "Encrypt sensitive data files"
                                })
                    except:
                        pass  # Skip if can't read file

                # Check for weak encryption in source code
                if file.endswith(('.py', '.js', '.java', '.go', '.rs')):
                    try:
                        content = file_path.read_text(encoding='utf-8')
                        for pattern in weak_crypto_patterns:
                            if re.search(pattern, content, re.IGNORECASE):
                                encryption_results["weak_encryption"].append({
                                    "file": str(file_path),
                                    "pattern": pattern,
                                    "recommendation": "Replace with stronger encryption algorithm"
                                })
                    except:
                        continue

    except Exception as e:
        encryption_results["error"] = str(e)

    # Add encryption recommendations
    encryption_results["encryption_recommendations"] = [
        "Use AES-256 for symmetric encryption",
        "Use RSA-2048 or higher for asymmetric encryption",
        "Implement proper key management",
        "Use TLS 1.2+ for data in transit",
        "Store encryption keys separately from encrypted data",
        "Regular key rotation policies"
    ]

    return encryption_results


async def review_authentication(config_files: List[str] = None, app_type: str = "web_application") -> Dict[str, Any]:
    """
    Review authentication mechanisms and configuration.

    Args:
        config_files: List of configuration files to review
        app_type: Type of application (web_application, api, mobile_app)

    Returns:
        Dict containing authentication review results
    """
    if config_files is None:
        config_files = []

    auth_review = {
        "strong_practices": [],
        "weak_practices": [],
        "missing_practices": [],
        "recommendations": []
    }

    # Authentication security patterns
    strong_auth_patterns = [
        r"bcrypt|scrypt|argon2",  # Strong password hashing
        r"multi.?factor|mfa|2fa",  # Multi-factor authentication
        r"oauth2|openid",  # OAuth implementation
        r"jwt.*HS256|RS256",  # JWT with strong algorithms
    ]

    weak_auth_patterns = [
        r"md5|sha1(?!256)",  # Weak password hashing
        r"password.*==.*['\"]",  # Hardcoded passwords
        r"session.*timeout.*[0-9]{7,}",  # Extremely long session timeouts
        r"jwt.*none",  # JWT without signature
    ]

    # Check configuration files
    for config_file in config_files:
        config_path = Path(config_file)
        if config_path.exists():
            try:
                content = config_path.read_text()

                # Check for strong authentication practices
                for pattern in strong_auth_patterns:
                    if re.search(pattern, content, re.IGNORECASE):
                        auth_review["strong_practices"].append({
                            "file": config_file,
                            "practice": pattern,
                            "status": "implemented"
                        })

                # Check for weak authentication practices
                for pattern in weak_auth_patterns:
                    if re.search(pattern, content, re.IGNORECASE):
                        auth_review["weak_practices"].append({
                            "file": config_file,
                            "issue": pattern,
                            "severity": "high"
                        })

            except Exception:
                continue

    # Application-specific recommendations
    app_recommendations = {
        "web_application": [
            "Implement multi-factor authentication",
            "Use strong password hashing (bcrypt, scrypt, argon2)",
            "Implement account lockout after failed attempts",
            "Use secure session management",
            "Implement CAPTCHA for brute force protection"
        ],
        "api": [
            "Use OAuth 2.0 or similar standard",
            "Implement JWT with strong signing algorithms",
            "Use API key authentication for service-to-service",
            "Implement rate limiting per authentication token",
            "Use HTTPS for all authentication endpoints"
        ],
        "mobile_app": [
            "Use biometric authentication where available",
            "Implement certificate pinning",
            "Use secure storage for tokens",
            "Implement app attestation",
            "Use short-lived tokens with refresh mechanism"
        ]
    }

    auth_review["recommendations"] = app_recommendations.get(app_type, app_recommendations["web_application"])

    # Add missing practices check
    required_practices = [
        "Strong password hashing",
        "Session timeout configuration",
        "Authentication logging",
        "Multi-factor authentication"
    ]

    for practice in required_practices:
        if not any(practice.lower() in str(p).lower() for p in auth_review["strong_practices"]):
            auth_review["missing_practices"].append({
                "practice": practice,
                "recommendation": f"Implement {practice.lower()}"
            })

    return auth_review


async def analyze_network_security(network_config: Dict[str, Any] = None) -> Dict[str, Any]:
    """
    Analyze network security configuration and setup.

    Args:
        network_config: Network configuration details

    Returns:
        Dict containing network security analysis
    """
    if network_config is None:
        network_config = {}

    network_analysis = {
        "security_measures": [],
        "vulnerabilities": [],
        "recommendations": []
    }

    # Common network security measures to check
    security_measures = {
        "firewall": "Network firewall configuration",
        "ssl_tls": "SSL/TLS encryption for communications",
        "vpn": "VPN access for remote connections",
        "network_segmentation": "Network segmentation and isolation",
        "intrusion_detection": "Intrusion detection/prevention system",
        "ddos_protection": "DDoS protection mechanisms"
    }

    # Check for implemented security measures
    for measure, description in security_measures.items():
        if measure in network_config and network_config[measure]:
            network_analysis["security_measures"].append({
                "measure": measure,
                "description": description,
                "status": "implemented"
            })
        else:
            network_analysis["vulnerabilities"].append({
                "missing_measure": measure,
                "description": description,
                "risk_level": "medium"
            })

    # Network security recommendations
    network_analysis["recommendations"] = [
        "Implement network firewall with least-privilege rules",
        "Use SSL/TLS for all network communications",
        "Implement network segmentation to isolate sensitive systems",
        "Deploy intrusion detection and prevention systems",
        "Regular network security assessments and penetration testing",
        "Monitor network traffic for suspicious activities",
        "Implement DDoS protection at network edge",
        "Use VPN for all remote access connections"
    ]

    # Specific recommendations based on missing measures
    for vuln in network_analysis["vulnerabilities"]:
        measure = vuln["missing_measure"]
        if measure == "firewall":
            network_analysis["recommendations"].append("URGENT: Deploy and configure network firewall")
        elif measure == "ssl_tls":
            network_analysis["recommendations"].append("HIGH PRIORITY: Enable SSL/TLS encryption")

    return network_analysis