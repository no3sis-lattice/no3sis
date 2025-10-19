#!/usr/bin/env python3
"""
Synapse Search Tool for Agent Integration
=========================================

A simple wrapper tool that agents can call to access the Synapse System's
intelligent context retrieval capabilities.

This tool implements the interface between agents and the complex hybrid system.
"""

import sys
import json
import subprocess
from pathlib import Path
from context_manager import SynapseContextManager

def activate_system():
    """
    Activate the no3sis system by running the activation script.
    This ensures the system is healthy and up-to-date before searching.
    """
    no3sis_root = Path.home() / ".no3sis-system"
    activate_script = no3sis_root / ".no3sis" / "neo4j" / "activate.sh"

    if not activate_script.exists():
        return False, "Activation script not found"

    try:
        # Run activation script
        result = subprocess.run(
            [str(activate_script)],
            capture_output=True,
            text=True,
            timeout=300  # 5 minute timeout
        )

        if result.returncode == 0:
            return True, "System activated successfully"
        else:
            return False, f"Activation failed: {result.stderr}"

    except subprocess.TimeoutExpired:
        return False, "Activation timed out"
    except Exception as e:
        return False, f"Activation error: {str(e)}"

def search_no3sis_context(query: str, max_results: int = 5, auto_activate: bool = False):
    """
    Main function for searching no3sis context.

    Args:
        query: The search query from the agent
        max_results: Maximum number of results to return
        auto_activate: Whether to automatically activate the system if needed

    Returns:
        Dict with search results and metadata
    """
    # Step 1: Auto-activate if requested
    if auto_activate:
        print("🔄 Activating Synapse System...", file=sys.stderr)
        success, message = activate_system()
        if not success:
            return {
                "error": "System activation failed",
                "details": message,
                "suggestion": "Try running the activation script manually"
            }
        print("✅ System activated", file=sys.stderr)

    # Step 2: Perform the search
    manager = SynapseContextManager()
    try:
        result = manager.intelligent_search(query, max_results)

        # Enhance the result with usage guidance
        if "context" in result and result["context"]:
            result["usage_guidance"] = generate_usage_guidance(result["context"])

        return result

    except Exception as e:
        return {
            "error": "Search failed",
            "details": str(e),
            "suggestion": "Check if services are running and try again"
        }
    finally:
        manager.close()

def generate_usage_guidance(context):
    """Generate usage guidance based on the search results"""
    guidance = []

    if "primary_matches" in context and context["primary_matches"]:
        guidance.append("📋 Primary matches found - these are most relevant to your query")

        for match in context["primary_matches"]:
            if match.get("type") == "md":
                guidance.append(f"📄 {match['file']}: Documentation/instruction file")
            elif match.get("type") == "sh":
                guidance.append(f"🔧 {match['file']}: Executable script")
            elif match.get("type") == "py":
                guidance.append(f"🐍 {match['file']}: Python implementation")

    if "related_files" in context and context["related_files"]:
        guidance.append("🔗 Related files discovered through graph relationships")

    if "suggested_actions" in context and context["suggested_actions"]:
        guidance.extend([f"💡 {action}" for action in context["suggested_actions"]])

    return guidance

def format_for_agent(result):
    """Format the result in a way that's optimal for agent consumption"""
    if "error" in result:
        return f"""❌ **Synapse Search Error**

{result['error']}: {result.get('details', 'No details available')}

💡 {result.get('suggestion', 'Try checking system status')}"""

    context = result.get("context", {})

    # Build formatted response
    response_parts = []

    # Header
    source_emoji = "💾" if result.get("source") == "cache" else "🔍"
    response_parts.append(f"{source_emoji} **Synapse Context** (Query: '{result.get('query', 'Unknown')}')")

    # Primary matches
    if context.get("primary_matches"):
        response_parts.append("\n### 📋 Primary Matches")
        for match in context["primary_matches"]:
            file_icon = "📄" if match.get("type") == "md" else "🔧" if match.get("type") == "sh" else "🐍" if match.get("type") == "py" else "📄"
            response_parts.append(f"- {file_icon} **{match['file']}** (`{match['path']}`)")
            response_parts.append(f"  - {match['summary']}")
            if match.get("word_count"):
                response_parts.append(f"  - Size: ~{match['word_count']} words")

    # Secondary matches
    if context.get("secondary_matches"):
        response_parts.append("\n### 📚 Secondary Matches")
        for match in context["secondary_matches"]:
            response_parts.append(f"- **{match['file']}**: {match['summary']}")

    # Related files
    if context.get("related_files"):
        response_parts.append("\n### 🔗 Related Files")
        for rel in context["related_files"][:3]:  # Limit to 3
            response_parts.append(f"- {rel['name']} (`{rel['path']}`)")

    # Key concepts
    if context.get("key_concepts"):
        concepts = ", ".join(context["key_concepts"][:5])
        response_parts.append(f"\n### 🔑 Key Concepts: {concepts}")

    # Usage guidance
    if "usage_guidance" in result:
        response_parts.append("\n### 💡 Usage Guidance")
        for guidance in result["usage_guidance"]:
            response_parts.append(f"- {guidance}")

    # Metadata
    response_parts.append(f"\n*Found {result.get('nodes_found', 0)} relevant files | Source: {result.get('source', 'unknown')}*")

    return "\n".join(response_parts)

def main():
    """CLI interface for the no3sis search tool"""
    if len(sys.argv) < 2:
        print("Usage: python no3sis_search.py <search_query> [max_results]")
        print("       python no3sis_search.py --help")
        print("       python no3sis_search.py --status")
        sys.exit(1)

    # Handle special commands
    if sys.argv[1] == "--help":
        print("""
Synapse Search Tool for Agent Integration

Usage:
  python no3sis_search.py <query>        Search for context
  python no3sis_search.py --status       Check system status
  python no3sis_search.py --activate     Activate system only
  python no3sis_search.py --help         Show this help

Examples:
  python no3sis_search.py "how to execute tasks"
  python no3sis_search.py "coding standards" 3
  python no3sis_search.py --status

The tool automatically activates the Synapse System before searching.
        """)
        sys.exit(0)

    elif sys.argv[1] == "--status":
        manager = SynapseContextManager()
        try:
            health = manager.check_health()
            print(json.dumps(health, indent=2))
        finally:
            manager.close()
        sys.exit(0)

    elif sys.argv[1] == "--activate":
        success, message = activate_system()
        print(f"Activation {'succeeded' if success else 'failed'}: {message}")
        sys.exit(0 if success else 1)

    # Parse arguments
    query = sys.argv[1]
    max_results = int(sys.argv[2]) if len(sys.argv) > 2 else 5

    # Perform search
    result = search_no3sis_context(query, max_results)

    # Output results
    if "--json" in sys.argv:
        print(json.dumps(result, indent=2))
    else:
        print(format_for_agent(result))

if __name__ == "__main__":
    main()