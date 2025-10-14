#!/usr/bin/env python3
"""
Synapse System Health Check
===========================

Comprehensive health check for the Synapse System in large codebases.
Verifies all components are working properly.
"""

import os
import sys
import json
import sqlite3
import subprocess
from pathlib import Path
import requests
from typing import Dict, List, Tuple, Optional

class SynapseHealthCheck:
    def __init__(self):
        self.synapse_root = Path.home() / ".synapse-system"
        self.neo4j_uri = "http://localhost:7474"
        self.redis_host = "localhost"
        self.redis_port = 6379
        self.results = []

    def check_component(self, name: str, check_func) -> bool:
        """Run a health check and record results"""
        try:
            success, message = check_func()
            status = "✅" if success else "❌"
            self.results.append({
                "component": name,
                "status": "pass" if success else "fail",
                "message": message
            })
            print(f"{status} {name}: {message}")
            return success
        except Exception as e:
            self.results.append({
                "component": name,
                "status": "error",
                "message": str(e)
            })
            print(f"❌ {name}: ERROR - {e}")
            return False

    def check_neo4j_service(self) -> Tuple[bool, str]:
        """Check if Neo4j is running and accessible"""
        try:
            response = requests.get(f"{self.neo4j_uri}/browser/", timeout=5)
            if response.status_code == 200:
                return True, "Neo4j service running"
            else:
                return False, f"Neo4j returned status {response.status_code}"
        except requests.ConnectionError:
            return False, "Neo4j service not accessible"
        except Exception as e:
            return False, f"Neo4j check failed: {e}"

    def check_redis_service(self) -> Tuple[bool, str]:
        """Check if Redis is running"""
        try:
            import redis
            client = redis.Redis(host=self.redis_host, port=self.redis_port, decode_responses=True)
            client.ping()
            return True, "Redis service running"
        except redis.exceptions.ConnectionError:
            return False, "Redis service not accessible"
        except ImportError:
            return False, "Redis Python client not installed"
        except Exception as e:
            return False, f"Redis check failed: {e}"

    def check_vector_store(self) -> Tuple[bool, str]:
        """Check vector store database"""
        vector_db_path = self.synapse_root / "neo4j" / "vector_store.db"
        if not vector_db_path.exists():
            return False, "Vector store database not found"

        try:
            conn = sqlite3.connect(vector_db_path)
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM vector_metadata")
            count = cursor.fetchone()[0]
            conn.close()

            if count > 0:
                return True, f"Vector store has {count} embeddings"
            else:
                return False, "Vector store is empty"
        except Exception as e:
            return False, f"Vector store check failed: {e}"

    def check_knowledge_graph(self) -> Tuple[bool, str]:
        """Check Neo4j knowledge graph data"""
        try:
            from neo4j import GraphDatabase
            driver = GraphDatabase.driver(
                "bolt://localhost:7687",
                auth=("neo4j", "synapse_neo4j_pass")
            )

            with driver.session() as session:
                result = session.run("MATCH (f:SynapseFile) RETURN count(f) as file_count")
                record = result.single()
                if record:
                    count = record["file_count"]
                    if count > 0:
                        return True, f"Knowledge graph has {count} files"
                    else:
                        return False, "Knowledge graph is empty"
                else:
                    return False, "Could not query knowledge graph"

        except Exception as e:
            return False, f"Knowledge graph check failed: {e}"
        finally:
            if 'driver' in locals():
                driver.close()

    def check_content_directories(self) -> Tuple[bool, str]:
        """Check if content directories exist and have files"""
        target_dirs = ["instructions", "standards", "workflows", "templates"]
        found_files = 0

        for dir_name in target_dirs:
            dir_path = self.synapse_root / ".synapse" / dir_name
            if dir_path.exists():
                files = list(dir_path.rglob("*.md"))
                found_files += len(files)

        if found_files > 0:
            return True, f"Found {found_files} content files"
        else:
            return False, "No content files found"

    def check_search_functionality(self) -> Tuple[bool, str]:
        """Test search functionality"""
        try:
            script_path = self.synapse_root / ".synapse" / "neo4j" / "synapse_search.py"
            if not script_path.exists():
                return False, "Search script not found"

            # Run a test search
            result = subprocess.run([
                sys.executable, str(script_path), "test"
            ], capture_output=True, text=True, timeout=30,
            env={**os.environ, "PYTHONPATH": str(script_path.parent)})

            if result.returncode == 0:
                # Check if results contain expected structure
                if "Synapse Context" in result.stdout:
                    return True, "Search functionality working"
                else:
                    return False, "Search runs but output format unexpected"
            else:
                return False, f"Search failed: {result.stderr}"

        except subprocess.TimeoutExpired:
            return False, "Search timed out"
        except Exception as e:
            return False, f"Search test failed: {e}"

    def check_bge_model(self) -> Tuple[bool, str]:
        """Check if BGE-M3 model loads correctly"""
        try:
            # Check if virtual environment exists
            venv_path = self.synapse_root / ".synapse" / "neo4j" / ".venv"
            if not venv_path.exists():
                return False, "Python virtual environment not found"

            # Check if BGE-M3 is importable in the venv
            vector_script = self.synapse_root / ".synapse" / "neo4j" / "vector_engine.py"
            if not vector_script.exists():
                return False, "Vector engine script not found"

            # Try a minimal import test
            test_script = """
import sys
sys.path.insert(0, '.')
try:
    from vector_engine import VectorEngine
    print("SUCCESS")
except Exception as e:
    print(f"FAILED: {e}")
"""
            result = subprocess.run([
                sys.executable, "-c", test_script
            ], cwd=self.synapse_root / ".synapse" / "neo4j",
            capture_output=True, text=True, timeout=10)

            if "SUCCESS" in result.stdout:
                return True, "BGE-M3 model environment ready"
            else:
                return False, f"Model import test failed: {result.stdout.strip()}"

        except subprocess.TimeoutExpired:
            return False, "Model check timed out"
        except Exception as e:
            return False, f"Model check failed: {e}"

    def run_full_check(self) -> Dict:
        """Run all health checks"""
        print("🔍 Synapse System Health Check")
        print("=" * 40)

        # Core services
        self.check_component("Neo4j Service", self.check_neo4j_service)
        self.check_component("Redis Service", self.check_redis_service)

        # Data stores
        self.check_component("Vector Store", self.check_vector_store)
        self.check_component("Knowledge Graph", self.check_knowledge_graph)

        # Content and functionality
        self.check_component("Content Directories", self.check_content_directories)
        self.check_component("Search Functionality", self.check_search_functionality)
        self.check_component("BGE-M3 Model", self.check_bge_model)

        # Summary
        passed = sum(1 for r in self.results if r["status"] == "pass")
        total = len(self.results)

        print("\n" + "=" * 40)
        print(f"Health Check Summary: {passed}/{total} checks passed")

        if passed == total:
            print("🎉 Synapse System is fully operational!")
            status = "healthy"
        elif passed >= total * 0.7:
            print("⚠️  Synapse System is mostly operational with minor issues")
            status = "degraded"
        else:
            print("❌ Synapse System has significant issues")
            status = "unhealthy"

        return {
            "status": status,
            "passed": passed,
            "total": total,
            "checks": self.results
        }

def main():
    """Main entry point"""
    if "--json" in sys.argv:
        # JSON output mode for scripting
        health_check = SynapseHealthCheck()
        result = health_check.run_full_check()
        print(json.dumps(result, indent=2))
    else:
        # Human-readable output
        health_check = SynapseHealthCheck()
        result = health_check.run_full_check()

        # Exit with appropriate code
        if result["status"] == "healthy":
            sys.exit(0)
        elif result["status"] == "degraded":
            sys.exit(1)
        else:
            sys.exit(2)

if __name__ == "__main__":
    main()