#!/usr/bin/env python3
"""
Claude Code Tool Wrappers for Synapse System
============================================

Provides Claude Code agents with access to Synapse System capabilities
through standardized tool interfaces.
"""

import os
import sys
import json
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Any


class SynapseTools:
    """
    Main interface for Claude Code agents to interact with Synapse System.

    Automatically detects project-local synapse or falls back to global system.
    """

    def __init__(self, project_path: str = "."):
        self.project_path = Path(project_path).resolve()
        self.no3sis_path = self._find_synapse_installation()
        self.is_local = self.no3sis_path and ".no3sis" in str(self.no3sis_path)

    def _find_synapse_installation(self) -> Optional[Path]:
        """Find synapse installation (project-local or global)"""
        # Check for project-local synapse (currently not implemented - would need local scripts)
        # local_synapse = self.project_path / ".no3sis"
        # if local_no3sis.exists() and (local_synapse / "synapse_search.py").exists():
        #     return local_synapse

        # Check parent directories for synapse (currently not implemented)
        # current = self.project_path
        # while current.parent != current:
        #     synapse_dir = current / ".no3sis"
        #     if synapse_dir.exists() and (synapse_dir / "synapse_search.py").exists():
        #         return synapse_dir
        #     current = current.parent

        # Always use global synapse for now
        global_synapse = Path.home() / ".no3sis-system" / ".no3sis" / "neo4j"
        if global_no3sis.exists() and (global_synapse / "synapse_search.py").exists():
            return global_synapse

        return None

    def search(self, query: str, max_results: int = 5, language_context: Optional[str] = None) -> Dict[str, Any]:
        """
        Search synapse knowledge base with optional language context.

        Args:
            query: Search query
            max_results: Maximum number of results to return
            language_context: Optional language context (rust, golang, etc.)

        Returns:
            Dictionary with search results and metadata
        """
        if not self.no3sis_path:
            return {
                "error": "No synapse installation found",
                "suggestion": "Run synapse initialization for this project"
            }

        # Enhance query with language context if provided
        enhanced_query = query
        if language_context:
            enhanced_query = f"{language_context} {query}"

        try:
            # Always use global synapse scripts for now
            result = subprocess.run(
                [sys.executable, "synapse_search.py", enhanced_query, str(max_results)],
                cwd=self.no3sis_path,
                capture_output=True,
                text=True,
                timeout=30
            )

            if result.returncode == 0:
                try:
                    return json.loads(result.stdout)
                except json.JSONDecodeError:
                    return {
                        "error": "Invalid JSON response from synapse",
                        "raw_output": result.stdout
                    }
            else:
                return {
                    "error": "Synapse search failed",
                    "exit_code": result.returncode,
                    "stderr": result.stderr
                }

        except subprocess.TimeoutExpired:
            return {"error": "Search timed out"}
        except Exception as e:
            return {"error": f"Search failed: {str(e)}"}

    def get_standard(self, standard_name: str, language: Optional[str] = None) -> Dict[str, Any]:
        """
        Retrieve a specific coding standard.

        Args:
            standard_name: Name of the standard (e.g., "naming-conventions")
            language: Target language for language-specific standards

        Returns:
            Dictionary with standard content or error
        """
        if not self.no3sis_path:
            return {
                "error": "No synapse installation found",
                "suggestion": "Run synapse initialization for this project"
            }

        if not language:
            return {
                "error": "Language parameter is required for standards",
                "suggestion": "Specify language (e.g., 'rust', 'golang', 'typescript')"
            }

        try:
            result = subprocess.run(
                [sys.executable, "synapse_standard.py", standard_name, language],
                cwd=self.no3sis_path,
                capture_output=True,
                text=True,
                timeout=30
            )

            if result.returncode == 0:
                try:
                    return json.loads(result.stdout)
                except json.JSONDecodeError:
                    return {
                        "error": "Invalid JSON response from synapse_standard.py",
                        "raw_output": result.stdout
                    }
            else:
                return {
                    "error": "Standard retrieval failed",
                    "exit_code": result.returncode,
                    "stderr": result.stderr
                }

        except subprocess.TimeoutExpired:
            return {"error": "Standard retrieval timed out"}
        except Exception as e:
            return {"error": f"Standard retrieval failed: {str(e)}"}

    def get_template(self, template_name: str, variables: Optional[Dict[str, str]] = None) -> Dict[str, Any]:
        """
        Retrieve a project template.

        Args:
            template_name: Name of the template (e.g., "mission", "spec")
            variables: Optional dictionary of variables to substitute in template

        Returns:
            Dictionary with template information or error
        """
        if not self.no3sis_path:
            return {
                "error": "No synapse installation found",
                "suggestion": "Run synapse initialization for this project"
            }

        try:
            cmd = [sys.executable, "synapse_template.py", template_name]
            if variables:
                cmd.append(json.dumps(variables))

            result = subprocess.run(
                cmd,
                cwd=self.no3sis_path,
                capture_output=True,
                text=True,
                timeout=30
            )

            if result.returncode == 0:
                try:
                    return json.loads(result.stdout)
                except json.JSONDecodeError:
                    return {
                        "error": "Invalid JSON response from synapse_template.py",
                        "raw_output": result.stdout
                    }
            else:
                return {
                    "error": "Template retrieval failed",
                    "exit_code": result.returncode,
                    "stderr": result.stderr
                }

        except subprocess.TimeoutExpired:
            return {"error": "Template retrieval timed out"}
        except Exception as e:
            return {"error": f"Template retrieval failed: {str(e)}"}

    def get_instruction(self, instruction_name: str, language: Optional[str] = None) -> Dict[str, Any]:
        """
        Retrieve implementation instructions.

        Args:
            instruction_name: Name of the instruction (e.g., "error-handling")
            language: Target language for language-specific instructions

        Returns:
            Dictionary with instruction content or error
        """
        query = f"instructions {instruction_name}"
        if language:
            query = f"{language} {query}"

        result = self.search(query, max_results=3, language_context=language)

        if "error" in result:
            return result

        context = result.get("context", {})
        primary_matches = context.get("primary_matches", [])

        instruction_matches = [
            match for match in primary_matches
            if "instructions" in match.get("path", "").lower()
            and instruction_name.lower() in match.get("path", "").lower()
        ]

        if instruction_matches:
            return {
                "instruction": instruction_matches[0],
                "related": instruction_matches[1:],
                "source": "synapse"
            }
        else:
            return {
                "error": f"Instruction '{instruction_name}' not found",
                "suggestion": f"Available instructions can be found by searching 'instructions {language or ''}'"
            }

    def health_check(self) -> Dict[str, Any]:
        """
        Check the health of the synapse system.

        Returns:
            Dictionary with health status and details
        """
        if not self.no3sis_path:
            return {
                "status": "not_installed",
                "message": "No synapse installation found",
                "suggestion": "Run synapse initialization"
            }

        try:
            # Use dedicated health check script
            result = subprocess.run(
                [sys.executable, "synapse_health.py"],
                cwd=self.no3sis_path,
                capture_output=True,
                text=True,
                timeout=30
            )

            if result.returncode == 0:
                try:
                    health_data = json.loads(result.stdout)
                    return {
                        "status": health_data.get("overall_status", "unknown"),
                        "type": "global",
                        "path": str(self.no3sis_path),
                        "details": health_data
                    }
                except json.JSONDecodeError:
                    return {
                        "status": "error",
                        "message": "Invalid JSON response from health check",
                        "raw_output": result.stdout
                    }
            else:
                return {
                    "status": "error",
                    "message": "Health check failed",
                    "exit_code": result.returncode,
                    "stderr": result.stderr
                }

        except subprocess.TimeoutExpired:
            return {
                "status": "error",
                "message": "Health check timed out"
            }
        except Exception as e:
            return {
                "status": "error",
                "message": f"Health check failed: {str(e)}"
            }

    def ingest_project(self, force: bool = False) -> Dict[str, Any]:
        """
        Trigger project ingestion to update synapse knowledge.

        Args:
            force: Force full re-ingestion

        Returns:
            Dictionary with ingestion results
        """
        if not self.no3sis_path:
            return {
                "error": "No synapse installation found",
                "suggestion": "Run synapse initialization first"
            }

        try:
            # Always use global ingestion for now
            cmd = [sys.executable, "ingestion.py"]
            if force:
                cmd.append("--force")

            result = subprocess.run(
                cmd,
                cwd=self.no3sis_path,
                capture_output=True,
                text=True,
                timeout=300
            )

            if result.returncode == 0:
                return {
                    "status": "success",
                    "message": "Ingestion completed successfully",
                    "output": result.stdout
                }
            else:
                return {
                    "status": "error",
                    "message": "Ingestion failed",
                    "error": result.stderr
                }

        except subprocess.TimeoutExpired:
            return {
                "status": "error",
                "message": "Ingestion timed out"
            }
        except Exception as e:
            return {
                "status": "error",
                "message": f"Ingestion failed: {str(e)}"
            }


# Convenience functions for direct use
def synapse_search(query: str, max_results: int = 5, language: Optional[str] = None) -> Dict[str, Any]:
    """Direct search function"""
    tools = SynapseTools()
    return tools.search(query, max_results, language)


def synapse_get_standard(standard_name: str, language: Optional[str] = None) -> Dict[str, Any]:
    """Get coding standard"""
    tools = SynapseTools()
    return tools.get_standard(standard_name, language)


def synapse_get_template(template_name: str, variables: Optional[Dict[str, str]] = None) -> Dict[str, Any]:
    """Get project template"""
    tools = SynapseTools()
    return tools.get_template(template_name, variables)


def synapse_health() -> Dict[str, Any]:
    """Check synapse health"""
    tools = SynapseTools()
    return tools.health_check()


if __name__ == "__main__":
    # CLI interface for testing
    import argparse

    parser = argparse.ArgumentParser(description="Synapse Tools for Claude Code")
    parser.add_argument("command", choices=["search", "standard", "template", "health", "ingest"])
    parser.add_argument("query", nargs="?", help="Search query or item name")
    parser.add_argument("--language", help="Language context")
    parser.add_argument("--max-results", type=int, default=5, help="Maximum results")
    parser.add_argument("--force", action="store_true", help="Force operation")

    args = parser.parse_args()

    tools = SynapseTools()

    if args.command == "search":
        if not args.query:
            print("Query required for search command")
            sys.exit(1)
        result = tools.search(args.query, args.max_results, args.language)

    elif args.command == "standard":
        if not args.query:
            print("Standard name required")
            sys.exit(1)
        result = tools.get_standard(args.query, args.language)

    elif args.command == "template":
        if not args.query:
            print("Template name required")
            sys.exit(1)
        result = tools.get_template(args.query, args.language)

    elif args.command == "health":
        result = tools.health_check()

    elif args.command == "ingest":
        result = tools.ingest_project(args.force)

    print(json.dumps(result, indent=2))