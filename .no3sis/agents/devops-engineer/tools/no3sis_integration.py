"""
DevOps Engineer Synapse Integration Tools

Connects DevOps Engineer to the broader Synapse knowledge graph for:
- Infrastructure pattern discovery and sharing
- CI/CD best practices and templates
- Deployment strategy recommendations
- Monitoring and operational knowledge sharing
"""

import sys
import asyncio
from pathlib import Path
from typing import Dict, Any, List, Optional

# Import Synapse search functionality
sys.path.append(str(Path.home() / ".no3sis-system" / ".no3sis" / "neo4j"))

try:
    from no3sis_search import search_synapse_context
    from context_manager import SynapseContextManager
    SYNAPSE_AVAILABLE = True
except ImportError:
    SYNAPSE_AVAILABLE = False
    print("⚠️  Synapse components not available, using mock implementations")


async def query_synapse_devops(query: str, context_type: str = "devops") -> Dict[str, Any]:
    """
    Search Synapse knowledge graph for DevOps-related information.

    Args:
        query: Search query for DevOps patterns, configs, or best practices
        context_type: Type of DevOps context (infrastructure, deployment, monitoring, etc.)

    Returns:
        Dict with relevant DevOps knowledge and recommendations
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_devops_search(query, context_type)

    try:
        # Enhance query with DevOps-specific terms
        enhanced_query = f"devops {context_type} {query} infrastructure deployment monitoring"

        results = search_synapse_context(
            query=enhanced_query,
            max_results=10,
            auto_activate=True
        )

        if "error" in results:
            return {
                "content": [{
                    "type": "text",
                    "text": f"DevOps knowledge search failed: {results['error']}"
                }],
                "knowledge_found": [],
                "recommendations": []
            }

        # Process results to extract DevOps-relevant information
        knowledge_items = _extract_devops_knowledge(results, query, context_type)
        recommendations = _generate_devops_recommendations(knowledge_items, query)

        return {
            "content": [{
                "type": "text",
                "text": f"Found {len(knowledge_items)} DevOps knowledge items for '{query}'"
            }],
            "knowledge_found": knowledge_items,
            "recommendations": recommendations,
            "context_type": context_type,
            "query_used": enhanced_query
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error querying DevOps knowledge: {e}"
            }],
            "knowledge_found": [],
            "error": str(e)
        }


async def search_deployment_patterns(deployment_type: str, technology: str = "") -> Dict[str, Any]:
    """
    Search for deployment patterns and best practices.

    Args:
        deployment_type: Type of deployment (blue-green, canary, rolling, etc.)
        technology: Technology stack (kubernetes, docker, aws, etc.)

    Returns:
        Dict with deployment patterns and implementation guides
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_deployment_patterns(deployment_type, technology)

    try:
        query = f"deployment pattern {deployment_type} {technology} strategy best practices"

        results = search_synapse_context(
            query=query,
            max_results=8,
            auto_activate=True
        )

        if "error" in results:
            return {
                "content": [{
                    "type": "text",
                    "text": f"Deployment pattern search failed: {results['error']}"
                }],
                "patterns": [],
                "implementation_guides": []
            }

        patterns = _extract_deployment_patterns(results, deployment_type, technology)
        guides = _extract_implementation_guides(results, deployment_type)

        return {
            "content": [{
                "type": "text",
                "text": f"Found {len(patterns)} deployment patterns for {deployment_type}"
            }],
            "deployment_type": deployment_type,
            "technology": technology,
            "patterns": patterns,
            "implementation_guides": guides,
            "best_practices": _get_deployment_best_practices(deployment_type)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error searching deployment patterns: {e}"
            }],
            "patterns": [],
            "error": str(e)
        }


async def search_infrastructure_knowledge(infrastructure_type: str, cloud_provider: str = "") -> Dict[str, Any]:
    """
    Search for infrastructure patterns and configurations.

    Args:
        infrastructure_type: Type of infrastructure (terraform, kubernetes, docker, etc.)
        cloud_provider: Cloud provider (aws, gcp, azure, etc.)

    Returns:
        Dict with infrastructure knowledge and configuration examples
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_infrastructure_search(infrastructure_type, cloud_provider)

    try:
        query = f"infrastructure {infrastructure_type} {cloud_provider} configuration terraform kubernetes"

        results = search_synapse_context(
            query=query,
            max_results=12,
            auto_activate=True
        )

        if "error" in results:
            return {
                "content": [{
                    "type": "text",
                    "text": f"Infrastructure knowledge search failed: {results['error']}"
                }],
                "configurations": [],
                "patterns": []
            }

        configurations = _extract_infrastructure_configs(results, infrastructure_type)
        patterns = _extract_infrastructure_patterns(results, infrastructure_type)

        return {
            "content": [{
                "type": "text",
                "text": f"Found {len(configurations)} infrastructure configurations for {infrastructure_type}"
            }],
            "infrastructure_type": infrastructure_type,
            "cloud_provider": cloud_provider,
            "configurations": configurations,
            "patterns": patterns,
            "security_considerations": _get_security_considerations(infrastructure_type),
            "cost_optimization": _get_cost_optimization_tips(infrastructure_type)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error searching infrastructure knowledge: {e}"
            }],
            "configurations": [],
            "error": str(e)
        }


async def search_monitoring_knowledge(monitoring_stack: str, metrics_type: str = "") -> Dict[str, Any]:
    """
    Search for monitoring configurations and best practices.

    Args:
        monitoring_stack: Monitoring technology (prometheus, elasticsearch, datadog, etc.)
        metrics_type: Type of metrics (application, infrastructure, business, etc.)

    Returns:
        Dict with monitoring knowledge and configuration examples
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_monitoring_search(monitoring_stack, metrics_type)

    try:
        query = f"monitoring {monitoring_stack} {metrics_type} observability metrics alerting"

        results = search_synapse_context(
            query=query,
            max_results=10,
            auto_activate=True
        )

        if "error" in results:
            return {
                "content": [{
                    "type": "text",
                    "text": f"Monitoring knowledge search failed: {results['error']}"
                }],
                "configurations": [],
                "best_practices": []
            }

        configurations = _extract_monitoring_configs(results, monitoring_stack)
        best_practices = _extract_monitoring_best_practices(results)

        return {
            "content": [{
                "type": "text",
                "text": f"Found {len(configurations)} monitoring configurations for {monitoring_stack}"
            }],
            "monitoring_stack": monitoring_stack,
            "metrics_type": metrics_type,
            "configurations": configurations,
            "best_practices": best_practices,
            "alerting_strategies": _get_alerting_strategies(monitoring_stack),
            "dashboard_templates": _get_dashboard_templates(monitoring_stack)
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error searching monitoring knowledge: {e}"
            }],
            "configurations": [],
            "error": str(e)
        }


async def publish_devops_knowledge(knowledge_item: Dict[str, Any], category: str = "general") -> Dict[str, Any]:
    """
    Share DevOps knowledge with the global knowledge graph.

    Args:
        knowledge_item: DevOps knowledge to share (config, pattern, lesson learned)
        category: Knowledge category (infrastructure, deployment, monitoring, security)

    Returns:
        Dict with publication status and assigned knowledge ID
    """
    if not SYNAPSE_AVAILABLE:
        return _mock_knowledge_publish(knowledge_item, category)

    try:
        # Create structured knowledge entry
        knowledge_entry = {
            "id": f"devops_{category}_{hash(str(knowledge_item)) % 10000}",
            "agent": "devops-engineer",
            "category": category,
            "type": knowledge_item.get("type", "configuration"),
            "title": knowledge_item.get("title", "DevOps Knowledge"),
            "content": knowledge_item.get("content", ""),
            "technologies": knowledge_item.get("technologies", []),
            "use_cases": knowledge_item.get("use_cases", []),
            "difficulty": knowledge_item.get("difficulty", "medium"),
            "reliability_score": knowledge_item.get("reliability", 0.8),
            "created_at": knowledge_item.get("created_at"),
            "tags": knowledge_item.get("tags", [])
        }

        # Store in knowledge graph
        success = await _store_devops_knowledge(knowledge_entry)

        if success:
            return {
                "content": [{
                    "type": "text",
                    "text": f"Published DevOps knowledge '{knowledge_entry['title']}' to knowledge graph"
                }],
                "published": True,
                "knowledge_id": knowledge_entry["id"],
                "knowledge_entry": knowledge_entry
            }
        else:
            return {
                "content": [{
                    "type": "text",
                    "text": "Failed to publish DevOps knowledge to graph"
                }],
                "published": False,
                "reason": "storage_error"
            }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error publishing DevOps knowledge: {e}"
            }],
            "published": False,
            "error": str(e)
        }


# Private helper functions

def _extract_devops_knowledge(results: Dict, query: str, context_type: str) -> List[Dict]:
    """Extract DevOps-relevant knowledge from search results."""
    knowledge_items = []

    context = results.get("context", [])
    for item in context:
        content = item.get("content", "")
        source = item.get("source", "unknown")

        # Look for DevOps patterns in content
        if any(term in content.lower() for term in ["infrastructure", "deployment", "ci/cd", "monitoring", "devops"]):
            knowledge_item = {
                "source": source,
                "relevance_score": item.get("similarity_score", 0.0),
                "content_snippet": content[:300] + "..." if len(content) > 300 else content,
                "context_type": context_type,
                "technologies": _extract_technologies_from_content(content)
            }
            knowledge_items.append(knowledge_item)

    return knowledge_items[:8]  # Limit to top 8


def _generate_devops_recommendations(knowledge_items: List[Dict], query: str) -> List[str]:
    """Generate recommendations based on found DevOps knowledge."""
    recommendations = []

    if not knowledge_items:
        recommendations.append(f"No existing knowledge found for '{query}' - consider documenting new approaches")
    elif len(knowledge_items) > 5:
        recommendations.append("Multiple approaches found - compare and select best fit for your use case")
    else:
        recommendations.append("Some relevant knowledge found - review for applicability to your context")

    recommendations.extend([
        "Validate configurations in non-production environment first",
        "Document any customizations for future reference",
        "Consider sharing successful implementations with the team"
    ])

    return recommendations


def _extract_deployment_patterns(results: Dict, deployment_type: str, technology: str) -> List[Dict]:
    """Extract deployment patterns from search results."""
    patterns = []

    for item in results.get("context", [])[:6]:
        pattern = {
            "name": f"{deployment_type}_pattern_{len(patterns)}",
            "technology": technology,
            "complexity": "medium",
            "rollback_strategy": "automatic",
            "description": item.get("content", "")[:200] + "...",
            "source": item.get("source", "unknown")
        }
        patterns.append(pattern)

    return patterns


def _extract_implementation_guides(results: Dict, deployment_type: str) -> List[Dict]:
    """Extract implementation guides from search results."""
    guides = []

    for item in results.get("context", [])[:4]:
        guide = {
            "title": f"{deployment_type.title()} Implementation Guide",
            "steps": [
                "Prepare deployment configuration",
                "Set up monitoring and alerts",
                "Execute deployment strategy",
                "Validate deployment success",
                "Monitor post-deployment metrics"
            ],
            "prerequisites": ["Docker", "CI/CD pipeline", "Monitoring setup"],
            "estimated_time": "2-4 hours",
            "source": item.get("source", "unknown")
        }
        guides.append(guide)

    return guides


def _extract_infrastructure_configs(results: Dict, infrastructure_type: str) -> List[Dict]:
    """Extract infrastructure configurations from search results."""
    configurations = []

    for item in results.get("context", [])[:5]:
        config = {
            "name": f"{infrastructure_type}_config_{len(configurations)}",
            "type": infrastructure_type,
            "environment": "production",
            "scalability": "high",
            "description": item.get("content", "")[:150] + "...",
            "source": item.get("source", "unknown")
        }
        configurations.append(config)

    return configurations


def _extract_infrastructure_patterns(results: Dict, infrastructure_type: str) -> List[Dict]:
    """Extract infrastructure patterns from search results."""
    patterns = []

    for item in results.get("context", [])[:4]:
        pattern = {
            "name": f"{infrastructure_type}_pattern",
            "use_case": "scalable_architecture",
            "benefits": ["High availability", "Cost efficiency", "Easy maintenance"],
            "considerations": ["Initial complexity", "Learning curve"],
            "source": item.get("source", "unknown")
        }
        patterns.append(pattern)

    return patterns


def _extract_monitoring_configs(results: Dict, monitoring_stack: str) -> List[Dict]:
    """Extract monitoring configurations from search results."""
    configurations = []

    for item in results.get("context", [])[:4]:
        config = {
            "stack": monitoring_stack,
            "metrics_collection": ["system", "application", "business"],
            "retention_period": "30 days",
            "alerting": "enabled",
            "description": item.get("content", "")[:200] + "...",
            "source": item.get("source", "unknown")
        }
        configurations.append(config)

    return configurations


def _extract_monitoring_best_practices(results: Dict) -> List[Dict]:
    """Extract monitoring best practices from search results."""
    best_practices = [
        {
            "practice": "Use SLI/SLO methodology",
            "description": "Define Service Level Indicators and Objectives for meaningful monitoring",
            "importance": "high"
        },
        {
            "practice": "Implement proper alerting thresholds",
            "description": "Avoid alert fatigue with well-tuned thresholds",
            "importance": "high"
        },
        {
            "practice": "Create runbooks for common issues",
            "description": "Document resolution steps for faster incident response",
            "importance": "medium"
        }
    ]

    return best_practices


def _extract_technologies_from_content(content: str) -> List[str]:
    """Extract technology names from content."""
    technologies = []
    tech_keywords = ["docker", "kubernetes", "terraform", "ansible", "jenkins", "prometheus", "grafana", "aws", "gcp", "azure"]

    for keyword in tech_keywords:
        if keyword.lower() in content.lower():
            technologies.append(keyword)

    return list(set(technologies))  # Remove duplicates


def _get_deployment_best_practices(deployment_type: str) -> List[str]:
    """Get best practices for deployment type."""
    practices = {
        "blue-green": [
            "Ensure identical environments for blue and green",
            "Implement automated health checks",
            "Have quick rollback mechanism ready"
        ],
        "canary": [
            "Start with small percentage of traffic",
            "Monitor key metrics closely",
            "Gradually increase traffic based on success metrics"
        ],
        "rolling": [
            "Update instances gradually",
            "Maintain minimum required capacity",
            "Implement proper health checks for new instances"
        ]
    }
    return practices.get(deployment_type, ["Follow general deployment best practices"])


def _get_security_considerations(infrastructure_type: str) -> List[str]:
    """Get security considerations for infrastructure type."""
    considerations = {
        "terraform": [
            "Store state files securely",
            "Use least privilege access policies",
            "Scan configurations for security issues"
        ],
        "kubernetes": [
            "Implement network policies",
            "Use security contexts appropriately",
            "Regularly update cluster and components"
        ],
        "docker": [
            "Use minimal base images",
            "Scan images for vulnerabilities",
            "Run containers as non-root users"
        ]
    }
    return considerations.get(infrastructure_type, ["Follow general security best practices"])


def _get_cost_optimization_tips(infrastructure_type: str) -> List[str]:
    """Get cost optimization tips for infrastructure type."""
    tips = {
        "terraform": [
            "Use appropriate instance sizes",
            "Implement auto-scaling policies",
            "Clean up unused resources regularly"
        ],
        "kubernetes": [
            "Set resource requests and limits",
            "Use cluster autoscaler",
            "Implement pod disruption budgets"
        ],
        "docker": [
            "Use multi-stage builds",
            "Optimize image layers",
            "Clean up unused images and containers"
        ]
    }
    return tips.get(infrastructure_type, ["Monitor and optimize resource usage"])


def _get_alerting_strategies(monitoring_stack: str) -> List[Dict]:
    """Get alerting strategies for monitoring stack."""
    strategies = [
        {
            "strategy": "Threshold-based alerting",
            "description": "Alert when metrics cross predefined thresholds",
            "use_case": "Simple metrics monitoring"
        },
        {
            "strategy": "Anomaly detection",
            "description": "Alert on unusual patterns in metrics",
            "use_case": "Complex system behavior monitoring"
        },
        {
            "strategy": "Composite alerts",
            "description": "Combine multiple conditions for more accurate alerts",
            "use_case": "Reducing false positive alerts"
        }
    ]
    return strategies


def _get_dashboard_templates(monitoring_stack: str) -> List[Dict]:
    """Get dashboard templates for monitoring stack."""
    templates = [
        {
            "name": "System Overview Dashboard",
            "metrics": ["CPU usage", "Memory usage", "Disk I/O", "Network I/O"],
            "target_audience": "Infrastructure team"
        },
        {
            "name": "Application Performance Dashboard",
            "metrics": ["Response time", "Throughput", "Error rate", "Apdex score"],
            "target_audience": "Development team"
        },
        {
            "name": "Business Metrics Dashboard",
            "metrics": ["User sessions", "Conversion rate", "Revenue impact", "Feature usage"],
            "target_audience": "Business stakeholders"
        }
    ]
    return templates


async def _store_devops_knowledge(knowledge_entry: Dict) -> bool:
    """Store DevOps knowledge in the knowledge graph."""
    try:
        # Store in local cache for now
        knowledge_cache = Path.home() / ".no3sis-system" / ".no3sis" / "devops_knowledge_cache.json"
        knowledge_cache.parent.mkdir(exist_ok=True)

        import json
        if knowledge_cache.exists():
            with open(knowledge_cache, 'r') as f:
                cache = json.load(f)
        else:
            cache = {"knowledge": []}

        cache["knowledge"].append(knowledge_entry)

        with open(knowledge_cache, 'w') as f:
            json.dump(cache, f, indent=2)

        return True

    except Exception as e:
        print(f"Error storing DevOps knowledge: {e}")
        return False


# Mock implementations for when Synapse is not available

def _mock_devops_search(query: str, context_type: str) -> Dict[str, Any]:
    """Mock DevOps knowledge search for testing."""
    return {
        "content": [{
            "type": "text",
            "text": f"Mock DevOps search for '{query}' (Synapse not available)"
        }],
        "knowledge_found": [{
            "source": "mock_devops_knowledge",
            "relevance_score": 0.7,
            "content_snippet": f"Mock DevOps knowledge for {query}",
            "context_type": context_type,
            "technologies": ["docker", "kubernetes"]
        }],
        "recommendations": [f"Mock recommendation for {query}"]
    }


def _mock_deployment_patterns(deployment_type: str, technology: str) -> Dict[str, Any]:
    """Mock deployment pattern search for testing."""
    return {
        "content": [{
            "type": "text",
            "text": f"Mock deployment patterns for {deployment_type}"
        }],
        "deployment_type": deployment_type,
        "technology": technology,
        "patterns": [{
            "name": f"mock_{deployment_type}_pattern",
            "technology": technology,
            "complexity": "medium",
            "description": f"Mock pattern for {deployment_type} deployment"
        }],
        "implementation_guides": [{
            "title": f"{deployment_type.title()} Mock Guide",
            "steps": ["Step 1", "Step 2", "Step 3"],
            "estimated_time": "2 hours"
        }]
    }


def _mock_infrastructure_search(infrastructure_type: str, cloud_provider: str) -> Dict[str, Any]:
    """Mock infrastructure knowledge search for testing."""
    return {
        "content": [{
            "type": "text",
            "text": f"Mock infrastructure knowledge for {infrastructure_type}"
        }],
        "infrastructure_type": infrastructure_type,
        "cloud_provider": cloud_provider,
        "configurations": [{
            "name": f"mock_{infrastructure_type}_config",
            "type": infrastructure_type,
            "description": f"Mock configuration for {infrastructure_type}"
        }],
        "patterns": [{
            "name": f"mock_{infrastructure_type}_pattern",
            "use_case": "scalable_architecture"
        }]
    }


def _mock_monitoring_search(monitoring_stack: str, metrics_type: str) -> Dict[str, Any]:
    """Mock monitoring knowledge search for testing."""
    return {
        "content": [{
            "type": "text",
            "text": f"Mock monitoring knowledge for {monitoring_stack}"
        }],
        "monitoring_stack": monitoring_stack,
        "metrics_type": metrics_type,
        "configurations": [{
            "stack": monitoring_stack,
            "description": f"Mock monitoring configuration for {monitoring_stack}"
        }],
        "best_practices": [{
            "practice": "Mock best practice",
            "importance": "high"
        }]
    }


def _mock_knowledge_publish(knowledge_item: Dict, category: str) -> Dict[str, Any]:
    """Mock knowledge publishing for testing."""
    return {
        "content": [{
            "type": "text",
            "text": f"Mock published DevOps knowledge: {knowledge_item.get('title', 'untitled')}"
        }],
        "published": True,
        "knowledge_id": f"mock_devops_{hash(str(knowledge_item)) % 10000}"
    }