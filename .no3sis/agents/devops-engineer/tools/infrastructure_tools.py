"""
Infrastructure Tools for DevOps Engineer Agent

Provides container management, CI/CD configuration, deployment, and monitoring capabilities.
"""

import json
import subprocess
import os
import yaml
from pathlib import Path
from typing import Dict, Any, List, Optional
from .mock_sdk import tool


@tool
async def manage_containers(action: str, container_name: str = "", options: Dict = None) -> Dict[str, Any]:
    """
    Manage Docker containers - build, run, stop, inspect.

    Args:
        action: Action to perform (build, run, stop, ps, inspect, logs)
        container_name: Name of container to manage
        options: Additional options for the action

    Returns:
        Dict with command results and status
    """
    if options is None:
        options = {}

    try:
        if action == "build":
            dockerfile_path = options.get("dockerfile", "Dockerfile")
            tag = options.get("tag", container_name or "latest")
            context = options.get("context", ".")

            cmd = ["docker", "build", "-t", tag, "-f", dockerfile_path, context]

        elif action == "run":
            image = options.get("image", container_name)
            ports = options.get("ports", [])
            env_vars = options.get("env", {})

            cmd = ["docker", "run", "-d"]

            # Add port mappings
            for port_map in ports:
                cmd.extend(["-p", port_map])

            # Add environment variables
            for key, value in env_vars.items():
                cmd.extend(["-e", f"{key}={value}"])

            if container_name:
                cmd.extend(["--name", container_name])

            cmd.append(image)

        elif action == "stop":
            cmd = ["docker", "stop", container_name]

        elif action == "ps":
            cmd = ["docker", "ps"]
            if options.get("all", False):
                cmd.append("-a")

        elif action == "inspect":
            cmd = ["docker", "inspect", container_name]

        elif action == "logs":
            cmd = ["docker", "logs", container_name]
            if options.get("follow", False):
                cmd.append("-f")

        else:
            return {
                "success": False,
                "error": f"Unknown action: {action}",
                "available_actions": ["build", "run", "stop", "ps", "inspect", "logs"]
            }

        # Execute command
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

        return {
            "success": result.returncode == 0,
            "command": " ".join(cmd),
            "output": result.stdout,
            "error": result.stderr if result.returncode != 0 else None,
            "returncode": result.returncode
        }

    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "error": "Command timed out after 60 seconds",
            "command": " ".join(cmd) if 'cmd' in locals() else action
        }
    except Exception as e:
        return {
            "success": False,
            "error": f"Error executing {action}: {str(e)}",
            "action": action
        }


@tool
async def configure_ci_cd(platform: str, config: Dict = None) -> Dict[str, Any]:
    """
    Generate CI/CD configuration files for various platforms.

    Args:
        platform: CI platform (github-actions, gitlab-ci, jenkins, travis)
        config: Configuration options for the pipeline

    Returns:
        Dict with generated config file content and path
    """
    if config is None:
        config = {}

    try:
        if platform == "github-actions":
            return await _generate_github_actions_config(config)
        elif platform == "gitlab-ci":
            return await _generate_gitlab_ci_config(config)
        elif platform == "jenkins":
            return await _generate_jenkins_config(config)
        elif platform == "travis":
            return await _generate_travis_config(config)
        else:
            return {
                "success": False,
                "error": f"Unsupported platform: {platform}",
                "supported_platforms": ["github-actions", "gitlab-ci", "jenkins", "travis"]
            }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error generating {platform} config: {str(e)}",
            "platform": platform
        }


@tool
async def deploy_services(environment: str, services: List[str], options: Dict = None) -> Dict[str, Any]:
    """
    Deploy services to specified environment using various deployment strategies.

    Args:
        environment: Target environment (dev, staging, prod)
        services: List of services to deploy
        options: Deployment options (strategy, replicas, etc.)

    Returns:
        Dict with deployment results and status
    """
    if options is None:
        options = {}

    try:
        strategy = options.get("strategy", "rolling")
        replicas = options.get("replicas", 1)

        deployment_results = []

        for service in services:
            if strategy == "blue-green":
                result = await _deploy_blue_green(service, environment, options)
            elif strategy == "canary":
                result = await _deploy_canary(service, environment, options)
            else:  # rolling deployment
                result = await _deploy_rolling(service, environment, options)

            deployment_results.append({
                "service": service,
                "strategy": strategy,
                **result
            })

        # Check if all deployments succeeded
        all_successful = all(r.get("success", False) for r in deployment_results)

        return {
            "success": all_successful,
            "environment": environment,
            "strategy": strategy,
            "deployments": deployment_results,
            "summary": f"Deployed {len([r for r in deployment_results if r.get('success')])} of {len(services)} services successfully"
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error deploying services: {str(e)}",
            "environment": environment,
            "services": services
        }


@tool
async def monitor_health(services: List[str], checks: Dict = None) -> Dict[str, Any]:
    """
    Monitor health of deployed services with various health check types.

    Args:
        services: List of services to monitor
        checks: Health check configuration (http, tcp, command)

    Returns:
        Dict with health status for each service
    """
    if checks is None:
        checks = {"type": "http", "path": "/health"}

    try:
        health_results = []

        for service in services:
            health_status = await _check_service_health(service, checks)
            health_results.append({
                "service": service,
                **health_status
            })

        # Calculate overall system health
        healthy_services = len([r for r in health_results if r.get("healthy", False)])
        overall_health = "healthy" if healthy_services == len(services) else "degraded" if healthy_services > 0 else "unhealthy"

        return {
            "overall_health": overall_health,
            "healthy_services": healthy_services,
            "total_services": len(services),
            "services": health_results,
            "timestamp": _get_timestamp()
        }

    except Exception as e:
        return {
            "overall_health": "unknown",
            "error": f"Error monitoring health: {str(e)}",
            "services": services
        }


@tool
async def scan_infrastructure(target: str, scan_type: str = "security") -> Dict[str, Any]:
    """
    Scan infrastructure for security vulnerabilities, compliance, or performance issues.

    Args:
        target: Target to scan (dockerfile, k8s-manifest, terraform, docker-image)
        scan_type: Type of scan (security, compliance, performance)

    Returns:
        Dict with scan results and recommendations
    """
    try:
        if target == "dockerfile":
            return await _scan_dockerfile(scan_type)
        elif target == "k8s-manifest":
            return await _scan_kubernetes(scan_type)
        elif target == "terraform":
            return await _scan_terraform(scan_type)
        elif target == "docker-image":
            return await _scan_docker_image(scan_type)
        else:
            return {
                "success": False,
                "error": f"Unsupported scan target: {target}",
                "supported_targets": ["dockerfile", "k8s-manifest", "terraform", "docker-image"]
            }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error scanning {target}: {str(e)}",
            "target": target,
            "scan_type": scan_type
        }


@tool
async def provision_resources(provider: str, resources: Dict, options: Dict = None) -> Dict[str, Any]:
    """
    Provision cloud resources using Infrastructure as Code.

    Args:
        provider: Cloud provider (aws, gcp, azure, terraform)
        resources: Resource definitions to provision
        options: Provisioning options (region, tags, etc.)

    Returns:
        Dict with provisioning results and resource information
    """
    if options is None:
        options = {}

    try:
        if provider == "terraform":
            return await _provision_with_terraform(resources, options)
        elif provider == "aws":
            return await _provision_aws_resources(resources, options)
        elif provider == "gcp":
            return await _provision_gcp_resources(resources, options)
        elif provider == "azure":
            return await _provision_azure_resources(resources, options)
        else:
            return {
                "success": False,
                "error": f"Unsupported provider: {provider}",
                "supported_providers": ["terraform", "aws", "gcp", "azure"]
            }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error provisioning with {provider}: {str(e)}",
            "provider": provider,
            "resources": list(resources.keys()) if resources else []
        }


# Helper functions

async def _generate_github_actions_config(config: Dict) -> Dict[str, Any]:
    """Generate GitHub Actions workflow configuration."""
    name = config.get("name", "CI/CD Pipeline")
    triggers = config.get("triggers", ["push", "pull_request"])
    language = config.get("language", "python")

    workflow = {
        "name": name,
        "on": triggers if isinstance(triggers, list) else [triggers],
        "jobs": {
            "build": {
                "runs-on": "ubuntu-latest",
                "steps": [
                    {"uses": "actions/checkout@v4"},
                    _get_language_setup_step(language),
                    {"name": "Install dependencies", "run": _get_install_command(language)},
                    {"name": "Run tests", "run": _get_test_command(language)},
                    {"name": "Build", "run": _get_build_command(language)}
                ]
            }
        }
    }

    config_content = yaml.dump(workflow, default_flow_style=False)

    return {
        "success": True,
        "config_file": ".github/workflows/ci.yml",
        "content": config_content,
        "platform": "github-actions"
    }


async def _generate_gitlab_ci_config(config: Dict) -> Dict[str, Any]:
    """Generate GitLab CI configuration."""
    language = config.get("language", "python")

    gitlab_config = {
        "stages": ["build", "test", "deploy"],
        "build": {
            "stage": "build",
            "script": [_get_install_command(language), _get_build_command(language)]
        },
        "test": {
            "stage": "test",
            "script": [_get_test_command(language)]
        },
        "deploy": {
            "stage": "deploy",
            "script": ["echo 'Deploying application'"],
            "only": ["main"]
        }
    }

    config_content = yaml.dump(gitlab_config, default_flow_style=False)

    return {
        "success": True,
        "config_file": ".gitlab-ci.yml",
        "content": config_content,
        "platform": "gitlab-ci"
    }


async def _generate_jenkins_config(config: Dict) -> Dict[str, Any]:
    """Generate Jenkins pipeline configuration."""
    language = config.get("language", "python")

    pipeline_script = f"""
pipeline {{
    agent any

    stages {{
        stage('Build') {{
            steps {{
                sh '{_get_install_command(language)}'
                sh '{_get_build_command(language)}'
            }}
        }}
        stage('Test') {{
            steps {{
                sh '{_get_test_command(language)}'
            }}
        }}
        stage('Deploy') {{
            steps {{
                echo 'Deploying application'
            }}
        }}
    }}
}}
"""

    return {
        "success": True,
        "config_file": "Jenkinsfile",
        "content": pipeline_script,
        "platform": "jenkins"
    }


async def _generate_travis_config(config: Dict) -> Dict[str, Any]:
    """Generate Travis CI configuration."""
    language = config.get("language", "python")

    travis_config = {
        "language": language,
        "install": [_get_install_command(language)],
        "script": [_get_test_command(language)],
        "deploy": {
            "provider": "script",
            "script": "echo 'Deploying application'",
            "on": {"branch": "main"}
        }
    }

    config_content = yaml.dump(travis_config, default_flow_style=False)

    return {
        "success": True,
        "config_file": ".travis.yml",
        "content": config_content,
        "platform": "travis"
    }


def _get_language_setup_step(language: str) -> Dict[str, str]:
    """Get language-specific setup step for GitHub Actions."""
    if language == "python":
        return {"uses": "actions/setup-python@v4", "with": {"python-version": "3.9"}}
    elif language == "node":
        return {"uses": "actions/setup-node@v3", "with": {"node-version": "16"}}
    elif language == "java":
        return {"uses": "actions/setup-java@v3", "with": {"java-version": "11"}}
    else:
        return {"name": f"Setup {language}", "run": f"echo 'Setting up {language}'"}


def _get_install_command(language: str) -> str:
    """Get language-specific install command."""
    commands = {
        "python": "pip install -r requirements.txt",
        "node": "npm install",
        "java": "mvn install -DskipTests",
        "go": "go mod download",
        "rust": "cargo build"
    }
    return commands.get(language, f"echo 'Install command for {language}'")


def _get_test_command(language: str) -> str:
    """Get language-specific test command."""
    commands = {
        "python": "python -m pytest",
        "node": "npm test",
        "java": "mvn test",
        "go": "go test ./...",
        "rust": "cargo test"
    }
    return commands.get(language, f"echo 'Test command for {language}'")


def _get_build_command(language: str) -> str:
    """Get language-specific build command."""
    commands = {
        "python": "python setup.py build",
        "node": "npm run build",
        "java": "mvn package",
        "go": "go build",
        "rust": "cargo build --release"
    }
    return commands.get(language, f"echo 'Build command for {language}'")


async def _deploy_blue_green(service: str, environment: str, options: Dict) -> Dict[str, Any]:
    """Implement blue-green deployment strategy."""
    return {
        "success": True,
        "strategy": "blue-green",
        "message": f"Blue-green deployment of {service} to {environment} completed",
        "active_slot": "blue" if options.get("current_slot") == "green" else "green"
    }


async def _deploy_canary(service: str, environment: str, options: Dict) -> Dict[str, Any]:
    """Implement canary deployment strategy."""
    traffic_percentage = options.get("canary_traffic", 10)
    return {
        "success": True,
        "strategy": "canary",
        "message": f"Canary deployment of {service} with {traffic_percentage}% traffic",
        "canary_traffic": traffic_percentage
    }


async def _deploy_rolling(service: str, environment: str, options: Dict) -> Dict[str, Any]:
    """Implement rolling deployment strategy."""
    replicas = options.get("replicas", 3)
    return {
        "success": True,
        "strategy": "rolling",
        "message": f"Rolling deployment of {service} with {replicas} replicas",
        "replicas": replicas
    }


async def _check_service_health(service: str, checks: Dict) -> Dict[str, Any]:
    """Check health of a specific service."""
    check_type = checks.get("type", "http")

    if check_type == "http":
        url = checks.get("url", f"http://{service}:8080{checks.get('path', '/health')}")
        return {
            "healthy": True,  # Mock response
            "response_time": 150,
            "status_code": 200,
            "check_type": "http",
            "endpoint": url
        }
    elif check_type == "tcp":
        port = checks.get("port", 8080)
        return {
            "healthy": True,  # Mock response
            "port": port,
            "check_type": "tcp",
            "connection_time": 50
        }
    else:
        return {
            "healthy": True,  # Mock response
            "check_type": check_type,
            "message": f"Custom health check for {service}"
        }


async def _scan_dockerfile(scan_type: str) -> Dict[str, Any]:
    """Scan Dockerfile for issues."""
    return {
        "success": True,
        "target": "dockerfile",
        "scan_type": scan_type,
        "issues_found": 2,
        "issues": [
            {"severity": "medium", "type": "base_image", "message": "Base image not pinned to specific version"},
            {"severity": "low", "type": "user", "message": "Running as root user"}
        ],
        "recommendations": [
            "Pin base image to specific version",
            "Create non-root user for application"
        ]
    }


async def _scan_kubernetes(scan_type: str) -> Dict[str, Any]:
    """Scan Kubernetes manifests."""
    return {
        "success": True,
        "target": "k8s-manifest",
        "scan_type": scan_type,
        "issues_found": 1,
        "issues": [
            {"severity": "high", "type": "security_context", "message": "securityContext not defined"}
        ],
        "recommendations": [
            "Add securityContext with runAsNonRoot: true"
        ]
    }


async def _scan_terraform(scan_type: str) -> Dict[str, Any]:
    """Scan Terraform configuration."""
    return {
        "success": True,
        "target": "terraform",
        "scan_type": scan_type,
        "issues_found": 3,
        "issues": [
            {"severity": "high", "type": "encryption", "message": "S3 bucket encryption not enabled"},
            {"severity": "medium", "type": "access", "message": "Overly permissive IAM policy"},
            {"severity": "low", "type": "versioning", "message": "S3 versioning not enabled"}
        ],
        "recommendations": [
            "Enable S3 bucket encryption",
            "Apply principle of least privilege to IAM policies",
            "Enable S3 versioning for data protection"
        ]
    }


async def _scan_docker_image(scan_type: str) -> Dict[str, Any]:
    """Scan Docker image for vulnerabilities."""
    return {
        "success": True,
        "target": "docker-image",
        "scan_type": scan_type,
        "vulnerabilities_found": 5,
        "vulnerabilities": [
            {"severity": "critical", "package": "openssl", "cve": "CVE-2023-1234"},
            {"severity": "high", "package": "curl", "cve": "CVE-2023-5678"},
        ],
        "recommendations": [
            "Update openssl to version 1.1.1t or later",
            "Update curl to version 7.88.0 or later"
        ]
    }


async def _provision_with_terraform(resources: Dict, options: Dict) -> Dict[str, Any]:
    """Provision resources using Terraform."""
    return {
        "success": True,
        "provider": "terraform",
        "resources_created": len(resources),
        "resources": [{"name": name, "type": config.get("type", "unknown")} for name, config in resources.items()],
        "state_file": "terraform.tfstate"
    }


async def _provision_aws_resources(resources: Dict, options: Dict) -> Dict[str, Any]:
    """Provision AWS resources."""
    return {
        "success": True,
        "provider": "aws",
        "region": options.get("region", "us-east-1"),
        "resources_created": len(resources),
        "resources": list(resources.keys())
    }


async def _provision_gcp_resources(resources: Dict, options: Dict) -> Dict[str, Any]:
    """Provision GCP resources."""
    return {
        "success": True,
        "provider": "gcp",
        "project": options.get("project", "default-project"),
        "resources_created": len(resources),
        "resources": list(resources.keys())
    }


async def _provision_azure_resources(resources: Dict, options: Dict) -> Dict[str, Any]:
    """Provision Azure resources."""
    return {
        "success": True,
        "provider": "azure",
        "resource_group": options.get("resource_group", "default-rg"),
        "resources_created": len(resources),
        "resources": list(resources.keys())
    }


def _get_timestamp() -> str:
    """Get current timestamp in ISO format."""
    from datetime import datetime
    return datetime.now().isoformat()