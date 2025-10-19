#!/usr/bin/env python3
"""
Synapse Health Check Tool
=========================

Quick health check tool for agents to verify Synapse System status.
Provides streamlined health information for agent decision-making.
"""

import sys
import json
import subprocess
import sqlite3
from pathlib import Path
from typing import Dict, Any, Tuple
import requests
import redis


def check_no3sis_health() -> Dict[str, Any]:
    """
    Perform comprehensive health check of the Synapse System.

    Returns:
        Dictionary with health status and component details
    """
    health_results = {
        "overall_status": "unknown",
        "timestamp": "",
        "components": {},
        "recommendations": []
    }

    from datetime import datetime
    health_results["timestamp"] = datetime.now().isoformat()

    # Check each component
    components_status = {}

    # 1. Neo4j Service
    neo4j_status, neo4j_message = check_neo4j_service()
    components_status["neo4j"] = {
        "status": "healthy" if neo4j_status else "unhealthy",
        "message": neo4j_message
    }

    # 2. Redis Service
    redis_status, redis_message = check_redis_service()
    components_status["redis"] = {
        "status": "healthy" if redis_status else "unhealthy",
        "message": redis_message
    }

    # 3. Vector Database
    vector_status, vector_message = check_vector_database()
    components_status["vector_db"] = {
        "status": "healthy" if vector_status else "unhealthy",
        "message": vector_message
    }

    # 4. Core Scripts
    scripts_status, scripts_message = check_core_scripts()
    components_status["core_scripts"] = {
        "status": "healthy" if scripts_status else "unhealthy",
        "message": scripts_message
    }

    # 5. Python Environment
    env_status, env_message = check_python_environment()
    components_status["python_env"] = {
        "status": "healthy" if env_status else "unhealthy",
        "message": env_message
    }

    health_results["components"] = components_status

    # Determine overall status
    healthy_components = sum(1 for comp in components_status.values() if comp["status"] == "healthy")
    total_components = len(components_status)

    if healthy_components == total_components:
        health_results["overall_status"] = "healthy"
    elif healthy_components >= total_components * 0.6:  # 60% threshold
        health_results["overall_status"] = "degraded"
    else:
        health_results["overall_status"] = "unhealthy"

    # Generate recommendations
    health_results["recommendations"] = generate_recommendations(components_status)

    return health_results


def check_neo4j_service() -> Tuple[bool, str]:
    """Check if Neo4j is running and accessible."""
    try:
        response = requests.get("http://localhost:7474", timeout=5)
        if response.status_code == 200:
            return True, "Neo4j service is running and accessible"
        else:
            return False, f"Neo4j service returned status {response.status_code}"
    except requests.exceptions.RequestException as e:
        return False, f"Neo4j service not accessible: {str(e)}"


def check_redis_service() -> Tuple[bool, str]:
    """Check if Redis is running and accessible."""
    try:
        r = redis.Redis(host='localhost', port=6379, decode_responses=True)
        r.ping()
        return True, "Redis service is running and accessible"
    except Exception as e:
        return False, f"Redis service not accessible: {str(e)}"


def check_vector_database() -> Tuple[bool, str]:
    """Check if the vector database is accessible."""
    no3sis_root = Path.home() / ".no3sis-system"
    vector_db_path = no3sis_root / "neo4j" / "vector_store.db"

    if not vector_db_path.exists():
        return False, "Vector database file not found"

    try:
        conn = sqlite3.connect(str(vector_db_path))
        cursor = conn.cursor()
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table';")
        tables = cursor.fetchall()
        conn.close()

        if tables:
            return True, f"Vector database accessible with {len(tables)} tables"
        else:
            return False, "Vector database exists but has no tables"
    except Exception as e:
        return False, f"Vector database error: {str(e)}"


def check_core_scripts() -> Tuple[bool, str]:
    """Check if core no3sis scripts exist and are executable."""
    no3sis_root = Path.home() / ".no3sis-system"
    neo4j_dir = no3sis_root / ".no3sis" / "neo4j"

    required_scripts = [
        "no3sis_search.py",
        "context_manager.py",
        "vector_engine.py",
        "no3sis_standard.py",
        "no3sis_template.py",
        "no3sis_health.py"
    ]

    missing_scripts = []
    for script in required_scripts:
        script_path = neo4j_dir / script
        if not script_path.exists():
            missing_scripts.append(script)

    if not missing_scripts:
        return True, "All core scripts are present"
    else:
        return False, f"Missing scripts: {', '.join(missing_scripts)}"


def check_python_environment() -> Tuple[bool, str]:
    """Check if Python environment is properly set up."""
    no3sis_root = Path.home() / ".no3sis-system"
    venv_path = no3sis_root / ".no3sis" / "neo4j" / ".venv"

    if not venv_path.exists():
        return False, "Python virtual environment not found"

    # Check if activate script exists
    activate_script = venv_path / "bin" / "activate"
    if not activate_script.exists():
        return False, "Virtual environment activate script not found"

    try:
        # Try to import key dependencies
        python_path = venv_path / "bin" / "python"
        if python_path.exists():
            result = subprocess.run(
                [str(python_path), "-c", "import neo4j, redis, sklearn"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                return True, "Python environment is properly configured"
            else:
                return False, f"Missing Python dependencies: {result.stderr}"
        else:
            return False, "Python interpreter not found in virtual environment"
    except Exception as e:
        return False, f"Python environment check failed: {str(e)}"


def generate_recommendations(components_status: Dict[str, Any]) -> list:
    """Generate actionable recommendations based on health check results."""
    recommendations = []

    for component, status in components_status.items():
        if status["status"] != "healthy":
            if component == "neo4j":
                recommendations.append("Start Neo4j service: ~/.no3sis-system/no3sis start")
            elif component == "redis":
                recommendations.append("Start Redis service: ~/.no3sis-system/no3sis start")
            elif component == "vector_db":
                recommendations.append("Initialize vector database: run ingestion.py")
            elif component == "core_scripts":
                recommendations.append("Reinstall no3sis system or check file permissions")
            elif component == "python_env":
                recommendations.append("Rebuild Python environment: cd ~/.no3sis-system/.no3sis/neo4j && ./activate.sh")

    if not recommendations:
        recommendations.append("System is healthy - all components are functioning properly")

    return recommendations


def main():
    """Command-line interface for the no3sis health check tool."""
    try:
        health_result = check_no3sis_health()
        print(json.dumps(health_result, indent=2))

        # Exit with error code if system is unhealthy
        if health_result["overall_status"] == "unhealthy":
            sys.exit(1)
        elif health_result["overall_status"] == "degraded":
            sys.exit(2)
        else:
            sys.exit(0)

    except Exception as e:
        error_result = {
            "overall_status": "error",
            "error": str(e),
            "recommendation": "Check no3sis installation and try again"
        }
        print(json.dumps(error_result, indent=2))
        sys.exit(3)


if __name__ == "__main__":
    main()