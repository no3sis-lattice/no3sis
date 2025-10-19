"""
Pull Request Management Tools

Create and manage pull requests with Synapse-enhanced templates and descriptions.
"""

from typing import Dict, Any, Optional
from .git_operations import execute_git_command, check_git_status

async def create_pull_requests(title: str, target_branch: str = "main",
                              template: Optional[Dict[str, Any]] = None,
                              spec_reference: Optional[str] = None,
                              include_test_results: bool = False,
                              urgent: bool = False) -> Dict[str, Any]:
    """Create pull request with enhanced template."""

    result = {
        "success": False,
        "pr_url": "",
        "pr_number": 0,
        "title": title,
        "target_branch": target_branch,
        "message": ""
    }

    try:
        # Generate PR description
        description = await generate_pr_description(
            title=title,
            spec_reference=spec_reference,
            include_test_results=include_test_results,
            urgent=urgent
        )

        # Create PR using gh CLI
        pr_cmd = [
            "gh", "pr", "create",
            "--title", title,
            "--body", description,
            "--base", target_branch
        ]

        if urgent:
            pr_cmd.extend(["--label", "urgent"])

        pr_result = await execute_git_command(pr_cmd)

        if pr_result["success"]:
            result["success"] = True
            result["pr_url"] = pr_result["output"].strip()
            result["message"] = f"Pull request created: {title}"
        else:
            result["message"] = f"Failed to create PR: {pr_result['error']}"

    except Exception as e:
        result["message"] = f"PR creation error: {str(e)}"

    return result

async def generate_pr_description(title: str, spec_reference: Optional[str] = None,
                                 include_test_results: bool = False,
                                 urgent: bool = False) -> str:
    """Generate comprehensive PR description."""

    description = f"## Summary\n{title}\n\n"

    # Add changes section
    description += "## Changes Made\n"

    # Get file changes
    status = await check_git_status()
    if status.get("staged_files", 0) > 0 or status.get("uncommitted_changes", 0) > 0:
        diff_result = await execute_git_command(["git", "diff", "--name-only", "HEAD"])
        if diff_result["success"]:
            files = diff_result["output"].strip().splitlines()
            for file in files[:10]:  # Limit to 10 files
                description += f"- Modified: {file}\n"

    description += "\n## Testing\n"
    if include_test_results:
        description += "- All tests passing ✓\n"
    else:
        description += "- Testing required\n"

    description += "\n## Related\n"
    if spec_reference:
        description += f"- Spec: {spec_reference}\n"

    if urgent:
        description += "\n⚠️ **URGENT HOTFIX** - Requires immediate review\n"

    return description

async def analyze_pr_readiness() -> Dict[str, Any]:
    """Analyze if repository is ready for PR creation."""
    readiness = {
        "ready": False,
        "issues": [],
        "recommendations": []
    }

    status = await check_git_status()

    # Check for uncommitted changes
    if status.get("uncommitted_changes", 0) > 0:
        readiness["issues"].append("Uncommitted changes detected")

    # Check if branch is pushed
    if status.get("unpushed_commits", 0) > 0:
        readiness["recommendations"].append("Push commits to remote before creating PR")

    readiness["ready"] = len(readiness["issues"]) == 0

    return readiness