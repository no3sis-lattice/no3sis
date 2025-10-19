"""
Monitoring Tools for DevOps Engineer Agent

Provides monitoring setup, health checking, log analysis, alerting, and reporting capabilities.
"""

import json
import time
import statistics
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, Any, List, Optional, Union
from .mock_sdk import tool


@tool
async def setup_monitoring(services: List[str], monitoring_config: Dict = None) -> Dict[str, Any]:
    """
    Set up comprehensive monitoring for services with various monitoring stacks.

    Args:
        services: List of services to monitor
        monitoring_config: Configuration for monitoring stack (prometheus, grafana, etc.)

    Returns:
        Dict with monitoring setup results and dashboard URLs
    """
    if monitoring_config is None:
        monitoring_config = {"stack": "prometheus", "retention": "30d"}

    try:
        stack = monitoring_config.get("stack", "prometheus")
        retention = monitoring_config.get("retention", "30d")

        if stack == "prometheus":
            return await _setup_prometheus_monitoring(services, monitoring_config)
        elif stack == "elasticsearch":
            return await _setup_elasticsearch_monitoring(services, monitoring_config)
        elif stack == "datadog":
            return await _setup_datadog_monitoring(services, monitoring_config)
        elif stack == "newrelic":
            return await _setup_newrelic_monitoring(services, monitoring_config)
        else:
            return {
                "success": False,
                "error": f"Unsupported monitoring stack: {stack}",
                "supported_stacks": ["prometheus", "elasticsearch", "datadog", "newrelic"]
            }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error setting up monitoring: {str(e)}",
            "services": services
        }


@tool
async def check_service_health(services: List[str], health_config: Dict = None) -> Dict[str, Any]:
    """
    Perform comprehensive health checks on services with various check types.

    Args:
        services: List of services to check
        health_config: Health check configuration (endpoints, timeouts, etc.)

    Returns:
        Dict with detailed health status for each service
    """
    if health_config is None:
        health_config = {"timeout": 30, "retries": 3}

    try:
        health_results = []
        timeout = health_config.get("timeout", 30)
        retries = health_config.get("retries", 3)

        for service in services:
            service_health = await _check_individual_service(service, health_config, timeout, retries)
            health_results.append({
                "service": service,
                **service_health
            })

        # Calculate overall system health metrics
        healthy_count = len([r for r in health_results if r.get("status") == "healthy"])
        degraded_count = len([r for r in health_results if r.get("status") == "degraded"])
        unhealthy_count = len([r for r in health_results if r.get("status") == "unhealthy"])

        overall_status = _determine_overall_health_status(healthy_count, degraded_count, unhealthy_count)

        return {
            "overall_status": overall_status,
            "timestamp": datetime.now().isoformat(),
            "summary": {
                "total_services": len(services),
                "healthy": healthy_count,
                "degraded": degraded_count,
                "unhealthy": unhealthy_count,
                "health_percentage": (healthy_count / len(services)) * 100 if services else 0
            },
            "services": health_results,
            "recommendations": _generate_health_recommendations(health_results)
        }

    except Exception as e:
        return {
            "overall_status": "error",
            "error": f"Error checking service health: {str(e)}",
            "services": services
        }


@tool
async def analyze_logs(log_source: str, analysis_config: Dict = None) -> Dict[str, Any]:
    """
    Analyze logs for patterns, errors, performance issues, and security concerns.

    Args:
        log_source: Source of logs (file path, service name, or log aggregation system)
        analysis_config: Analysis configuration (time range, patterns, severity levels)

    Returns:
        Dict with log analysis results, patterns, and recommendations
    """
    if analysis_config is None:
        analysis_config = {"time_range": "1h", "include_errors": True}

    try:
        time_range = analysis_config.get("time_range", "1h")
        include_errors = analysis_config.get("include_errors", True)
        include_warnings = analysis_config.get("include_warnings", True)
        pattern_detection = analysis_config.get("pattern_detection", True)

        # Parse time range
        time_window = _parse_time_range(time_range)

        # Analyze log entries
        log_analysis = await _analyze_log_entries(log_source, time_window, analysis_config)

        # Detect patterns and anomalies
        patterns = await _detect_log_patterns(log_analysis["entries"]) if pattern_detection else []

        # Generate insights and recommendations
        insights = _generate_log_insights(log_analysis, patterns)

        return {
            "success": True,
            "log_source": log_source,
            "time_range": time_range,
            "analysis_period": {
                "start": time_window["start"].isoformat(),
                "end": time_window["end"].isoformat()
            },
            "summary": {
                "total_entries": log_analysis["total_entries"],
                "error_count": log_analysis["error_count"],
                "warning_count": log_analysis["warning_count"],
                "unique_patterns": len(patterns)
            },
            "top_errors": log_analysis.get("top_errors", []),
            "patterns": patterns,
            "insights": insights,
            "recommendations": _generate_log_recommendations(log_analysis, patterns)
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error analyzing logs: {str(e)}",
            "log_source": log_source
        }


@tool
async def create_alerts(alert_rules: List[Dict], alert_config: Dict = None) -> Dict[str, Any]:
    """
    Create monitoring alerts with various notification channels and escalation policies.

    Args:
        alert_rules: List of alert rule definitions
        alert_config: Alert configuration (channels, thresholds, escalation)

    Returns:
        Dict with created alerts and notification setup
    """
    if alert_config is None:
        alert_config = {"channels": ["email"], "severity_mapping": {"critical": ["email", "slack"]}}

    try:
        created_alerts = []
        notification_channels = alert_config.get("channels", ["email"])
        severity_mapping = alert_config.get("severity_mapping", {})

        for rule in alert_rules:
            alert_result = await _create_individual_alert(rule, alert_config)

            if alert_result.get("success", False):
                created_alerts.append({
                    "alert_name": rule.get("name", "unnamed_alert"),
                    "alert_id": alert_result["alert_id"],
                    "severity": rule.get("severity", "medium"),
                    "channels": _get_channels_for_severity(rule.get("severity", "medium"), severity_mapping, notification_channels),
                    "status": "active"
                })

        # Set up notification channels
        channel_setup = await _setup_notification_channels(notification_channels, alert_config)

        return {
            "success": True,
            "alerts_created": len(created_alerts),
            "alerts": created_alerts,
            "notification_channels": channel_setup,
            "escalation_policy": _create_escalation_policy(alert_config),
            "summary": f"Created {len(created_alerts)} alerts with {len(notification_channels)} notification channels"
        }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error creating alerts: {str(e)}",
            "alert_rules_count": len(alert_rules)
        }


@tool
async def generate_reports(report_type: str, report_config: Dict = None) -> Dict[str, Any]:
    """
    Generate various types of monitoring and performance reports.

    Args:
        report_type: Type of report (performance, availability, security, cost)
        report_config: Report configuration (time period, services, metrics)

    Returns:
        Dict with generated report data and visualizations
    """
    if report_config is None:
        report_config = {"period": "7d", "format": "json"}

    try:
        period = report_config.get("period", "7d")
        report_format = report_config.get("format", "json")
        services = report_config.get("services", [])

        if report_type == "performance":
            return await _generate_performance_report(period, services, report_config)
        elif report_type == "availability":
            return await _generate_availability_report(period, services, report_config)
        elif report_type == "security":
            return await _generate_security_report(period, services, report_config)
        elif report_type == "cost":
            return await _generate_cost_report(period, services, report_config)
        elif report_type == "summary":
            return await _generate_summary_report(period, services, report_config)
        else:
            return {
                "success": False,
                "error": f"Unsupported report type: {report_type}",
                "supported_types": ["performance", "availability", "security", "cost", "summary"]
            }

    except Exception as e:
        return {
            "success": False,
            "error": f"Error generating {report_type} report: {str(e)}",
            "report_type": report_type
        }


# Helper functions

async def _setup_prometheus_monitoring(services: List[str], config: Dict) -> Dict[str, Any]:
    """Set up Prometheus monitoring stack."""
    monitoring_config = {
        "prometheus": {
            "retention": config.get("retention", "30d"),
            "scrape_interval": config.get("scrape_interval", "15s"),
            "targets": [f"{service}:8080/metrics" for service in services]
        },
        "grafana": {
            "dashboards": len(services),
            "datasources": ["prometheus"],
            "url": "http://localhost:3000"
        },
        "alertmanager": {
            "rules": len(services) * 3,  # Basic alerts per service
            "routes": ["email", "slack"]
        }
    }

    return {
        "success": True,
        "monitoring_stack": "prometheus",
        "services_monitored": len(services),
        "configuration": monitoring_config,
        "dashboards": [
            {"name": f"{service}-overview", "url": f"http://localhost:3000/d/{service}"} for service in services
        ],
        "metrics_endpoints": [f"{service}:8080/metrics" for service in services]
    }


async def _setup_elasticsearch_monitoring(services: List[str], config: Dict) -> Dict[str, Any]:
    """Set up Elasticsearch/ELK monitoring stack."""
    return {
        "success": True,
        "monitoring_stack": "elasticsearch",
        "services_monitored": len(services),
        "configuration": {
            "elasticsearch": {"indices": f"logs-{'-'.join(services)}", "retention": config.get("retention", "30d")},
            "logstash": {"pipelines": len(services), "processors": ["json", "grok", "date"]},
            "kibana": {"dashboards": len(services), "url": "http://localhost:5601"}
        }
    }


async def _setup_datadog_monitoring(services: List[str], config: Dict) -> Dict[str, Any]:
    """Set up Datadog monitoring."""
    return {
        "success": True,
        "monitoring_stack": "datadog",
        "services_monitored": len(services),
        "configuration": {
            "agents": len(services),
            "metrics": ["system", "application", "custom"],
            "logs": {"enabled": True, "retention": config.get("retention", "30d")}
        }
    }


async def _setup_newrelic_monitoring(services: List[str], config: Dict) -> Dict[str, Any]:
    """Set up New Relic monitoring."""
    return {
        "success": True,
        "monitoring_stack": "newrelic",
        "services_monitored": len(services),
        "configuration": {
            "apm_services": len(services),
            "infrastructure_monitoring": True,
            "alerting": {"policies": len(services), "channels": ["email", "slack"]}
        }
    }


async def _check_individual_service(service: str, config: Dict, timeout: int, retries: int) -> Dict[str, Any]:
    """Check health of individual service with retries."""
    health_checks = config.get("checks", ["http", "tcp"])
    endpoints = config.get("endpoints", {})

    # Simulate health check results
    http_check = await _perform_http_health_check(service, endpoints.get("http", f"http://{service}:8080/health"))
    tcp_check = await _perform_tcp_health_check(service, endpoints.get("tcp", f"{service}:8080"))
    custom_checks = await _perform_custom_health_checks(service, config.get("custom", []))

    # Aggregate health status
    all_checks = [http_check, tcp_check] + custom_checks
    healthy_checks = len([c for c in all_checks if c.get("status") == "healthy"])

    if healthy_checks == len(all_checks):
        status = "healthy"
    elif healthy_checks > len(all_checks) / 2:
        status = "degraded"
    else:
        status = "unhealthy"

    return {
        "status": status,
        "checks": {
            "http": http_check,
            "tcp": tcp_check,
            "custom": custom_checks
        },
        "response_times": {
            "avg": statistics.mean([c.get("response_time", 0) for c in all_checks if c.get("response_time")]),
            "max": max([c.get("response_time", 0) for c in all_checks if c.get("response_time")], default=0)
        },
        "last_check": datetime.now().isoformat()
    }


async def _perform_http_health_check(service: str, endpoint: str) -> Dict[str, Any]:
    """Perform HTTP health check."""
    return {
        "type": "http",
        "endpoint": endpoint,
        "status": "healthy",
        "status_code": 200,
        "response_time": 120,
        "content_length": 45
    }


async def _perform_tcp_health_check(service: str, endpoint: str) -> Dict[str, Any]:
    """Perform TCP health check."""
    return {
        "type": "tcp",
        "endpoint": endpoint,
        "status": "healthy",
        "connection_time": 50,
        "port_open": True
    }


async def _perform_custom_health_checks(service: str, custom_checks: List[Dict]) -> List[Dict[str, Any]]:
    """Perform custom health checks."""
    results = []
    for check in custom_checks:
        results.append({
            "type": "custom",
            "name": check.get("name", "unnamed"),
            "status": "healthy",
            "response_time": 80
        })
    return results


def _determine_overall_health_status(healthy: int, degraded: int, unhealthy: int) -> str:
    """Determine overall system health status."""
    total = healthy + degraded + unhealthy
    if total == 0:
        return "unknown"

    healthy_percentage = healthy / total
    if healthy_percentage >= 0.9:
        return "healthy"
    elif healthy_percentage >= 0.7:
        return "degraded"
    else:
        return "unhealthy"


def _generate_health_recommendations(health_results: List[Dict]) -> List[str]:
    """Generate recommendations based on health check results."""
    recommendations = []

    unhealthy_services = [r["service"] for r in health_results if r.get("status") == "unhealthy"]
    degraded_services = [r["service"] for r in health_results if r.get("status") == "degraded"]

    if unhealthy_services:
        recommendations.append(f"Immediate attention required for unhealthy services: {', '.join(unhealthy_services)}")

    if degraded_services:
        recommendations.append(f"Monitor degraded services closely: {', '.join(degraded_services)}")

    # Check for high response times
    high_response_services = [
        r["service"] for r in health_results
        if r.get("response_times", {}).get("avg", 0) > 1000
    ]

    if high_response_services:
        recommendations.append(f"Performance optimization needed for: {', '.join(high_response_services)}")

    if not recommendations:
        recommendations.append("All services are healthy - continue monitoring")

    return recommendations


def _parse_time_range(time_range: str) -> Dict[str, datetime]:
    """Parse time range string into datetime objects."""
    now = datetime.now()

    if time_range.endswith('h'):
        hours = int(time_range[:-1])
        start = now - timedelta(hours=hours)
    elif time_range.endswith('d'):
        days = int(time_range[:-1])
        start = now - timedelta(days=days)
    elif time_range.endswith('w'):
        weeks = int(time_range[:-1])
        start = now - timedelta(weeks=weeks)
    else:
        start = now - timedelta(hours=1)  # Default to 1 hour

    return {"start": start, "end": now}


async def _analyze_log_entries(log_source: str, time_window: Dict, config: Dict) -> Dict[str, Any]:
    """Analyze log entries within time window."""
    # Mock log analysis results
    return {
        "total_entries": 15420,
        "error_count": 45,
        "warning_count": 120,
        "info_count": 15255,
        "top_errors": [
            {"message": "Database connection timeout", "count": 15, "severity": "error"},
            {"message": "Rate limit exceeded", "count": 12, "severity": "warning"},
            {"message": "Cache miss", "count": 8, "severity": "info"}
        ],
        "entries": [
            {"timestamp": time_window["start"].isoformat(), "level": "error", "message": "Sample error"},
            {"timestamp": time_window["end"].isoformat(), "level": "info", "message": "Sample info"}
        ]
    }


async def _detect_log_patterns(log_entries: List[Dict]) -> List[Dict[str, Any]]:
    """Detect patterns in log entries."""
    return [
        {
            "pattern": "Database timeout spike",
            "frequency": "high",
            "confidence": 0.85,
            "time_correlation": "peak_hours",
            "recommendation": "Scale database connections during peak hours"
        },
        {
            "pattern": "API rate limiting",
            "frequency": "medium",
            "confidence": 0.92,
            "time_correlation": "business_hours",
            "recommendation": "Implement client-side retry logic with exponential backoff"
        }
    ]


def _generate_log_insights(log_analysis: Dict, patterns: List[Dict]) -> List[str]:
    """Generate insights from log analysis."""
    insights = []

    error_rate = log_analysis["error_count"] / log_analysis["total_entries"]
    if error_rate > 0.01:  # More than 1% errors
        insights.append(f"High error rate detected: {error_rate:.2%}")

    if patterns:
        insights.append(f"Detected {len(patterns)} recurring patterns requiring attention")

    if log_analysis["warning_count"] > 100:
        insights.append("High warning count may indicate emerging issues")

    return insights


def _generate_log_recommendations(log_analysis: Dict, patterns: List[Dict]) -> List[str]:
    """Generate recommendations based on log analysis."""
    recommendations = []

    for pattern in patterns:
        recommendations.append(pattern.get("recommendation", "Review pattern manually"))

    if log_analysis["error_count"] > 0:
        recommendations.append("Investigate top error messages for root cause analysis")

    recommendations.append("Consider setting up automated alerting for critical error patterns")

    return recommendations


async def _create_individual_alert(rule: Dict, config: Dict) -> Dict[str, Any]:
    """Create individual alert rule."""
    alert_id = f"alert_{hash(str(rule)) % 10000}"

    return {
        "success": True,
        "alert_id": alert_id,
        "rule": rule.get("name", "unnamed"),
        "condition": rule.get("condition", ""),
        "threshold": rule.get("threshold", ""),
        "notification_delay": config.get("notification_delay", "5m")
    }


def _get_channels_for_severity(severity: str, severity_mapping: Dict, default_channels: List[str]) -> List[str]:
    """Get notification channels based on alert severity."""
    return severity_mapping.get(severity, default_channels)


async def _setup_notification_channels(channels: List[str], config: Dict) -> Dict[str, Any]:
    """Set up notification channels."""
    channel_configs = {}

    for channel in channels:
        if channel == "email":
            channel_configs["email"] = {
                "type": "email",
                "recipients": config.get("email_recipients", ["devops@company.com"]),
                "template": "standard"
            }
        elif channel == "slack":
            channel_configs["slack"] = {
                "type": "slack",
                "webhook_url": config.get("slack_webhook", "https://hooks.slack.com/..."),
                "channel": config.get("slack_channel", "#alerts")
            }
        elif channel == "webhook":
            channel_configs["webhook"] = {
                "type": "webhook",
                "url": config.get("webhook_url", ""),
                "method": "POST"
            }

    return channel_configs


def _create_escalation_policy(config: Dict) -> Dict[str, Any]:
    """Create escalation policy for alerts."""
    return {
        "levels": [
            {"level": 1, "wait_time": "5m", "channels": ["email"]},
            {"level": 2, "wait_time": "15m", "channels": ["email", "slack"]},
            {"level": 3, "wait_time": "30m", "channels": ["email", "slack", "webhook"]}
        ],
        "max_escalations": config.get("max_escalations", 3),
        "repeat_interval": config.get("repeat_interval", "1h")
    }


async def _generate_performance_report(period: str, services: List[str], config: Dict) -> Dict[str, Any]:
    """Generate performance report."""
    return {
        "success": True,
        "report_type": "performance",
        "period": period,
        "services": services or ["all"],
        "metrics": {
            "avg_response_time": "245ms",
            "p95_response_time": "850ms",
            "throughput": "1,250 req/min",
            "error_rate": "0.45%"
        },
        "trends": {
            "response_time": "stable",
            "throughput": "increasing",
            "error_rate": "decreasing"
        },
        "bottlenecks": [
            {"service": "database", "issue": "connection pool exhaustion", "impact": "high"},
            {"service": "cache", "issue": "memory pressure", "impact": "medium"}
        ]
    }


async def _generate_availability_report(period: str, services: List[str], config: Dict) -> Dict[str, Any]:
    """Generate availability report."""
    return {
        "success": True,
        "report_type": "availability",
        "period": period,
        "services": services or ["all"],
        "sla_metrics": {
            "overall_uptime": "99.87%",
            "planned_downtime": "0.05%",
            "unplanned_downtime": "0.08%",
            "mttr": "12.5 minutes",
            "mtbf": "7.2 days"
        },
        "incidents": [
            {"date": "2024-09-20", "duration": "15 minutes", "cause": "database failover", "impact": "partial"},
            {"date": "2024-09-18", "duration": "8 minutes", "cause": "deployment rollback", "impact": "minimal"}
        ]
    }


async def _generate_security_report(period: str, services: List[str], config: Dict) -> Dict[str, Any]:
    """Generate security report."""
    return {
        "success": True,
        "report_type": "security",
        "period": period,
        "services": services or ["all"],
        "security_metrics": {
            "vulnerabilities": {
                "critical": 0,
                "high": 2,
                "medium": 8,
                "low": 15
            },
            "security_events": 45,
            "blocked_requests": 1250,
            "failed_logins": 85
        },
        "recommendations": [
            "Update dependencies with high severity vulnerabilities",
            "Review and strengthen authentication policies",
            "Implement additional rate limiting for API endpoints"
        ]
    }


async def _generate_cost_report(period: str, services: List[str], config: Dict) -> Dict[str, Any]:
    """Generate cost report."""
    return {
        "success": True,
        "report_type": "cost",
        "period": period,
        "services": services or ["all"],
        "cost_metrics": {
            "total_cost": "$1,245.67",
            "cost_per_service": {"api": "$456.78", "database": "$342.10", "cache": "$156.34", "monitoring": "$290.45"},
            "cost_trends": {
                "vs_previous_period": "+8.5%",
                "vs_same_period_last_year": "+23.4%"
            }
        },
        "optimization_opportunities": [
            {"service": "database", "potential_savings": "$85/month", "recommendation": "Right-size instance"},
            {"service": "storage", "potential_savings": "$45/month", "recommendation": "Implement lifecycle policies"}
        ]
    }


async def _generate_summary_report(period: str, services: List[str], config: Dict) -> Dict[str, Any]:
    """Generate summary report combining all metrics."""
    return {
        "success": True,
        "report_type": "summary",
        "period": period,
        "services": services or ["all"],
        "executive_summary": {
            "overall_health": "good",
            "uptime": "99.87%",
            "performance": "stable",
            "security_posture": "strong",
            "cost_efficiency": "optimizing"
        },
        "key_metrics": {
            "availability": "99.87%",
            "avg_response_time": "245ms",
            "error_rate": "0.45%",
            "security_events": 45,
            "monthly_cost": "$1,245.67"
        },
        "action_items": [
            "Address 2 high-severity vulnerabilities",
            "Optimize database connection pooling",
            "Review cost optimization opportunities"
        ]
    }