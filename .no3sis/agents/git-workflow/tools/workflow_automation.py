"""
Workflow Automation Tools

Complete git workflow automation for feature development, hotfixes, and releases.
Implements Agent OS conventions with intelligent branch naming and PR creation.
"""

import re
from pathlib import Path
from typing import Dict, List, Any, Optional
from .git_operations import (
    manage_branches, create_commits, check_git_status, execute_git_command
)
from .pr_management import create_pull_requests

async def execute_git_workflow(action: str, spec_folder: Optional[str] = None,
                              target_branch: str = "main",
                              pr_title: Optional[str] = None) -> Dict[str, Any]:
    """
    Execute complete git workflow from changes to PR creation.

    Args:
        action: Workflow type (feature, hotfix, release)
        spec_folder: Path to spec folder for branch naming
        target_branch: Target branch for PR
        pr_title: Custom PR title

    Returns:
        Complete workflow execution result
    """
    workflow_result = {
        "action": action,
        "success": False,
        "steps_completed": [],
        "branch_created": "",
        "commit_hash": "",
        "pr_url": "",
        "warnings": [],
        "message": ""
    }

    try:
        if action == "feature":
            result = await create_feature_workflow(spec_folder, target_branch, pr_title)
        elif action == "hotfix":
            result = await create_hotfix_workflow(spec_folder, target_branch, pr_title)
        elif action == "release":
            result = await create_release_workflow(target_branch)
        else:
            workflow_result["message"] = f"Unknown workflow action: {action}"
            return workflow_result

        # Merge results
        workflow_result.update(result)

    except Exception as e:
        workflow_result["message"] = f"Workflow execution error: {str(e)}"

    return workflow_result

async def create_feature_workflow(spec_folder: Optional[str] = None,
                                target_branch: str = "main",
                                pr_title: Optional[str] = None) -> Dict[str, Any]:
    """
    Execute feature development workflow with Agent OS conventions.

    Args:
        spec_folder: Path to spec folder (e.g., ".agent-os/specs/2025-01-29-feature-name/")
        target_branch: Target branch for PR
        pr_title: Custom PR title

    Returns:
        Feature workflow execution result
    """
    result = {
        "success": False,
        "steps_completed": [],
        "branch_created": "",
        "commit_hash": "",
        "pr_url": "",
        "warnings": [],
        "message": ""
    }

    try:
        # Step 1: Determine branch name
        branch_name = _extract_branch_name_from_spec(spec_folder) if spec_folder else "feature-branch"
        result["branch_created"] = branch_name

        # Step 2: Check current repository status
        status = await check_git_status()

        # Step 3: Handle branch creation/switching
        current_branch = status.get("current_branch", "")

        if current_branch == branch_name:
            # Already on the right branch
            result["steps_completed"].append(f"✓ Already on branch: {branch_name}")
        elif current_branch in ["main", "master", "staging"]:
            # On main branch, create feature branch
            branch_result = await manage_branches("create", branch_name, target_branch)
            if branch_result["success"]:
                result["steps_completed"].append(f"✓ Created branch: {branch_name}")
            else:
                result["message"] = f"Failed to create branch: {branch_result['message']}"
                return result
        else:
            # On different feature branch, ask user or switch
            result["warnings"].append(f"Currently on branch '{current_branch}', switching to '{branch_name}'")
            branch_result = await manage_branches("switch", branch_name)
            if not branch_result["success"]:
                # Branch doesn't exist, create it
                branch_result = await manage_branches("create", branch_name, target_branch)

            if branch_result["success"]:
                result["steps_completed"].append(f"✓ Switched to branch: {branch_name}")
            else:
                result["message"] = f"Failed to manage branch: {branch_result['message']}"
                return result

        # Step 4: Check for changes to commit
        updated_status = await check_git_status()
        if updated_status.get("uncommitted_changes", 0) == 0 and updated_status.get("untracked_files", 0) == 0:
            result["warnings"].append("No changes detected to commit")
        else:
            # Step 5: Create commit
            commit_message = _generate_commit_message(spec_folder, "feature")
            commit_result = await create_commits(commit_message)

            if commit_result["success"]:
                result["commit_hash"] = commit_result["commit_hash"]
                result["steps_completed"].append(f"✓ Created commit: {commit_message}")
            else:
                result["message"] = f"Failed to create commit: {commit_result.get('message', 'Unknown error')}"
                return result

        # Step 6: Push to remote
        push_result = await execute_git_command(["git", "push", "-u", "origin", branch_name])
        if push_result["success"]:
            result["steps_completed"].append(f"✓ Pushed to origin/{branch_name}")
        else:
            result["warnings"].append(f"Failed to push: {push_result['error']}")

        # Step 7: Create pull request
        pr_title_final = pr_title or _generate_pr_title(spec_folder, "feature")
        pr_result = await create_pull_requests(
            title=pr_title_final,
            target_branch=target_branch,
            spec_reference=spec_folder
        )

        if pr_result["success"]:
            result["pr_url"] = pr_result["pr_url"]
            result["steps_completed"].append(f"✓ Created PR: {pr_title_final}")
            result["success"] = True
            result["message"] = f"Feature workflow completed successfully"
        else:
            result["warnings"].append(f"PR creation failed: {pr_result.get('message', 'Unknown error')}")
            result["success"] = True  # Workflow mostly successful
            result["message"] = "Feature workflow completed (PR creation failed)"

    except Exception as e:
        result["message"] = f"Feature workflow error: {str(e)}"

    return result

async def create_hotfix_workflow(spec_folder: Optional[str] = None,
                               target_branch: str = "main",
                               pr_title: Optional[str] = None) -> Dict[str, Any]:
    """
    Execute hotfix workflow for urgent production fixes.

    Args:
        spec_folder: Path to spec folder
        target_branch: Target branch (usually main/production)
        pr_title: Custom PR title

    Returns:
        Hotfix workflow execution result
    """
    result = {
        "success": False,
        "steps_completed": [],
        "branch_created": "",
        "commit_hash": "",
        "pr_url": "",
        "warnings": [],
        "message": ""
    }

    try:
        # Hotfix branches start with "hotfix-"
        branch_name = f"hotfix-{_extract_branch_name_from_spec(spec_folder)}" if spec_folder else "hotfix-urgent"
        result["branch_created"] = branch_name

        # Ensure we start from the target branch (usually main)
        checkout_result = await execute_git_command(["git", "checkout", target_branch])
        if not checkout_result["success"]:
            result["message"] = f"Failed to checkout {target_branch}: {checkout_result['error']}"
            return result

        # Pull latest changes
        pull_result = await execute_git_command(["git", "pull", "origin", target_branch])
        if pull_result["success"]:
            result["steps_completed"].append(f"✓ Pulled latest from {target_branch}")

        # Create hotfix branch
        branch_result = await manage_branches("create", branch_name, target_branch)
        if not branch_result["success"]:
            result["message"] = f"Failed to create hotfix branch: {branch_result['message']}"
            return result

        result["steps_completed"].append(f"✓ Created hotfix branch: {branch_name}")

        # Commit changes
        commit_message = _generate_commit_message(spec_folder, "hotfix")
        commit_result = await create_commits(commit_message)

        if commit_result["success"]:
            result["commit_hash"] = commit_result["commit_hash"]
            result["steps_completed"].append(f"✓ Created hotfix commit: {commit_message}")
        else:
            result["message"] = f"Failed to create commit: {commit_result.get('message', 'Unknown error')}"
            return result

        # Push hotfix branch
        push_result = await execute_git_command(["git", "push", "-u", "origin", branch_name])
        if push_result["success"]:
            result["steps_completed"].append(f"✓ Pushed hotfix branch")

        # Create urgent PR
        pr_title_final = pr_title or _generate_pr_title(spec_folder, "hotfix")
        pr_result = await create_pull_requests(
            title=pr_title_final,
            target_branch=target_branch,
            spec_reference=spec_folder,
            urgent=True
        )

        if pr_result["success"]:
            result["pr_url"] = pr_result["pr_url"]
            result["steps_completed"].append(f"✓ Created urgent PR: {pr_title_final}")

        result["success"] = True
        result["message"] = "Hotfix workflow completed successfully"

    except Exception as e:
        result["message"] = f"Hotfix workflow error: {str(e)}"

    return result

async def create_release_workflow(target_branch: str = "main") -> Dict[str, Any]:
    """
    Execute release workflow with version tagging.

    Args:
        target_branch: Branch to release from

    Returns:
        Release workflow execution result
    """
    result = {
        "success": False,
        "steps_completed": [],
        "release_version": "",
        "tag_created": "",
        "warnings": [],
        "message": ""
    }

    try:
        # Ensure clean working directory
        status = await check_git_status()
        if not status.get("clean", False):
            result["message"] = "Working directory not clean - commit or stash changes first"
            return result

        # Switch to target branch
        checkout_result = await execute_git_command(["git", "checkout", target_branch])
        if not checkout_result["success"]:
            result["message"] = f"Failed to checkout {target_branch}"
            return result

        # Pull latest changes
        pull_result = await execute_git_command(["git", "pull", "origin", target_branch])
        if pull_result["success"]:
            result["steps_completed"].append(f"✓ Pulled latest from {target_branch}")

        # Determine next version
        version = await _determine_next_version()
        result["release_version"] = version

        # Create release tag
        tag_result = await execute_git_command([
            "git", "tag", "-a", f"v{version}", "-m", f"Release version {version}"
        ])

        if tag_result["success"]:
            result["tag_created"] = f"v{version}"
            result["steps_completed"].append(f"✓ Created tag: v{version}")

            # Push tag
            push_tag_result = await execute_git_command(["git", "push", "origin", f"v{version}"])
            if push_tag_result["success"]:
                result["steps_completed"].append(f"✓ Pushed tag to remote")

        result["success"] = True
        result["message"] = f"Release workflow completed for version {version}"

    except Exception as e:
        result["message"] = f"Release workflow error: {str(e)}"

    return result

# Helper functions

def _extract_branch_name_from_spec(spec_folder: Optional[str]) -> str:
    """Extract branch name from spec folder path following Agent OS conventions."""
    if not spec_folder:
        return "feature-branch"

    # Handle paths like ".agent-os/specs/2025-01-29-feature-name/"
    path = Path(spec_folder)
    folder_name = path.name

    # Remove date prefix if present (2025-01-29-feature-name -> feature-name)
    date_pattern = r'^\d{4}-\d{2}-\d{2}-'
    branch_name = re.sub(date_pattern, '', folder_name)

    # Ensure kebab-case
    branch_name = re.sub(r'[_\s]+', '-', branch_name.lower())

    return branch_name or "feature-branch"

def _generate_commit_message(spec_folder: Optional[str], workflow_type: str) -> str:
    """Generate intelligent commit message based on spec and workflow type."""
    if spec_folder:
        feature_name = _extract_branch_name_from_spec(spec_folder)
        feature_display = feature_name.replace('-', ' ').title()

        if workflow_type == "feature":
            return f"feat: implement {feature_display}"
        elif workflow_type == "hotfix":
            return f"fix: urgent {feature_display} hotfix"
        elif workflow_type == "release":
            return f"release: {feature_display}"

    # Fallback messages
    fallback_messages = {
        "feature": "feat: implement new functionality",
        "hotfix": "fix: urgent production fix",
        "release": "release: new version"
    }

    return fallback_messages.get(workflow_type, "update: code changes")

def _generate_pr_title(spec_folder: Optional[str], workflow_type: str) -> str:
    """Generate PR title based on spec and workflow type."""
    if spec_folder:
        feature_name = _extract_branch_name_from_spec(spec_folder)
        feature_display = feature_name.replace('-', ' ').title()

        if workflow_type == "feature":
            return f"Add {feature_display}"
        elif workflow_type == "hotfix":
            return f"[HOTFIX] Fix {feature_display}"

    # Fallback titles
    fallback_titles = {
        "feature": "Add new feature",
        "hotfix": "[HOTFIX] Urgent production fix"
    }

    return fallback_titles.get(workflow_type, "Update code")

async def _determine_next_version() -> str:
    """Determine next semantic version based on git tags."""
    # Get latest tag
    tag_result = await execute_git_command([
        "git", "describe", "--tags", "--abbrev=0"
    ])

    if tag_result["success"]:
        latest_tag = tag_result["output"].strip()
        # Remove 'v' prefix if present
        version_str = latest_tag.lstrip('v')

        # Parse semantic version (major.minor.patch)
        parts = version_str.split('.')
        if len(parts) >= 3:
            try:
                major, minor, patch = int(parts[0]), int(parts[1]), int(parts[2])
                # Increment patch version
                return f"{major}.{minor}.{patch + 1}"
            except ValueError:
                pass

    # Default to 1.0.0 if no valid tags found
    return "1.0.0"

async def validate_workflow_prerequisites(workflow_type: str) -> Dict[str, Any]:
    """Validate prerequisites before executing workflow."""
    validation = {
        "valid": True,
        "issues": [],
        "warnings": []
    }

    # Check git repository
    status = await check_git_status()
    if "error" in status:
        validation["valid"] = False
        validation["issues"].append("Not in a git repository")
        return validation

    # Check for remote repository
    if not status.get("remote_exists", False):
        validation["warnings"].append("No remote repository configured")

    # Workflow-specific validations
    if workflow_type == "hotfix":
        # Ensure on main/production branch
        current_branch = status.get("current_branch", "")
        if current_branch not in ["main", "master", "production"]:
            validation["warnings"].append(f"Hotfix usually starts from main branch (currently on {current_branch})")

    elif workflow_type == "release":
        # Ensure clean working directory
        if not status.get("clean", False):
            validation["valid"] = False
            validation["issues"].append("Working directory must be clean for release")

        # Check if ahead of remote
        if status.get("unpushed_commits", 0) > 0:
            validation["warnings"].append("Local commits not pushed to remote")

    return validation

async def cleanup_workflow_artifacts(branch_name: str, keep_branch: bool = False) -> Dict[str, Any]:
    """Clean up workflow artifacts after completion."""
    cleanup_result = {
        "success": False,
        "actions_taken": [],
        "warnings": []
    }

    try:
        # Switch to main branch first
        checkout_result = await execute_git_command(["git", "checkout", "main"])
        if checkout_result["success"]:
            cleanup_result["actions_taken"].append("Switched to main branch")

        # Delete feature branch if requested
        if not keep_branch and branch_name not in ["main", "master", "staging"]:
            delete_result = await manage_branches("delete", branch_name)
            if delete_result["success"]:
                cleanup_result["actions_taken"].append(f"Deleted branch: {branch_name}")
            else:
                cleanup_result["warnings"].append(f"Failed to delete branch: {branch_name}")

        cleanup_result["success"] = True

    except Exception as e:
        cleanup_result["warnings"].append(f"Cleanup error: {str(e)}")

    return cleanup_result