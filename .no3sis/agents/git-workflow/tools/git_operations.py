"""
Git Operations Tools

Core git functionality with safety checks and intelligent automation.
Implements secure git operations with comprehensive error handling.
"""

import asyncio
import subprocess
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from datetime import datetime

async def manage_branches(action: str, branch_name: Optional[str] = None,
                         source_branch: Optional[str] = None) -> Dict[str, Any]:
    """
    Manage git branches with intelligent naming and safety checks.

    Args:
        action: Action to perform (create, switch, delete, list)
        branch_name: Name of branch
        source_branch: Source branch for new branches

    Returns:
        Operation result with branch information
    """
    result = {
        "action": action,
        "success": False,
        "branch_name": branch_name,
        "message": "",
        "branches": [],
        "current_branch": "",
        "warnings": []
    }

    try:
        # Get current branch first
        current_result = await execute_git_command(["git", "branch", "--show-current"])
        if current_result["success"]:
            result["current_branch"] = current_result["output"].strip()

        if action == "list":
            branches_result = await execute_git_command(["git", "branch", "-a"])
            if branches_result["success"]:
                branches = []
                for line in branches_result["output"].splitlines():
                    branch = line.strip().lstrip('* ').replace('remotes/origin/', '')
                    if branch and not branch.startswith('HEAD'):
                        branches.append(branch)
                result["branches"] = list(set(branches))  # Remove duplicates
                result["success"] = True
                result["message"] = f"Found {len(result['branches'])} branches"

        elif action == "create":
            if not branch_name:
                result["message"] = "Branch name required for create action"
                return result

            # Validate branch name
            if not _is_valid_branch_name(branch_name):
                result["message"] = f"Invalid branch name: {branch_name}"
                result["warnings"].append("Use kebab-case, no dates, no special characters")
                return result

            # Check if branch already exists
            existing_result = await execute_git_command(["git", "branch", "--list", branch_name])
            if existing_result["success"] and existing_result["output"].strip():
                result["message"] = f"Branch '{branch_name}' already exists"
                return result

            # Check for uncommitted changes
            status_check = await check_git_status()
            if status_check.get("uncommitted_changes", 0) > 0:
                result["warnings"].append(f"Uncommitted changes detected ({status_check['uncommitted_changes']} files)")

            # Create branch
            source = source_branch or result["current_branch"]
            if source and source != result["current_branch"]:
                # Switch to source branch first
                checkout_result = await execute_git_command(["git", "checkout", source])
                if not checkout_result["success"]:
                    result["message"] = f"Failed to switch to source branch: {source}"
                    return result

            create_result = await execute_git_command(["git", "checkout", "-b", branch_name])
            if create_result["success"]:
                result["success"] = True
                result["message"] = f"Created and switched to branch: {branch_name}"
                result["current_branch"] = branch_name
            else:
                result["message"] = f"Failed to create branch: {create_result['error']}"

        elif action == "switch":
            if not branch_name:
                result["message"] = "Branch name required for switch action"
                return result

            # Check for uncommitted changes
            status_check = await check_git_status()
            if status_check.get("uncommitted_changes", 0) > 0:
                result["warnings"].append("Uncommitted changes will be carried over to new branch")

            switch_result = await execute_git_command(["git", "checkout", branch_name])
            if switch_result["success"]:
                result["success"] = True
                result["message"] = f"Switched to branch: {branch_name}"
                result["current_branch"] = branch_name
            else:
                result["message"] = f"Failed to switch branch: {switch_result['error']}"

        elif action == "delete":
            if not branch_name:
                result["message"] = "Branch name required for delete action"
                return result

            # Safety check - don't delete current branch
            if branch_name == result["current_branch"]:
                result["message"] = f"Cannot delete current branch: {branch_name}"
                return result

            # Check if branch is merged
            merged_result = await execute_git_command(["git", "branch", "--merged"])
            is_merged = branch_name in merged_result.get("output", "")

            if not is_merged:
                result["warnings"].append(f"Branch '{branch_name}' is not merged")

            delete_result = await execute_git_command(["git", "branch", "-d", branch_name])
            if delete_result["success"]:
                result["success"] = True
                result["message"] = f"Deleted branch: {branch_name}"
            else:
                # Try force delete if regular delete failed
                force_delete_result = await execute_git_command(["git", "branch", "-D", branch_name])
                if force_delete_result["success"]:
                    result["success"] = True
                    result["message"] = f"Force deleted branch: {branch_name}"
                    result["warnings"].append("Branch was force deleted (unmerged changes lost)")
                else:
                    result["message"] = f"Failed to delete branch: {delete_result['error']}"

        else:
            result["message"] = f"Unknown action: {action}"

    except Exception as e:
        result["message"] = f"Error in branch operation: {str(e)}"

    return result

async def create_commits(message: str, files: Optional[List[str]] = None,
                        amend: bool = False) -> Dict[str, Any]:
    """
    Create git commits with intelligent staging and message validation.

    Args:
        message: Commit message
        files: Specific files to commit (None for all changes)
        amend: Whether to amend the last commit

    Returns:
        Commit operation result
    """
    result = {
        "success": False,
        "message": message,
        "files_committed": [],
        "commit_hash": "",
        "warnings": [],
        "stats": {}
    }

    try:
        # Check repository status
        status = await check_git_status()
        if status.get("uncommitted_changes", 0) == 0 and not amend:
            result["message"] = "No changes to commit"
            return result

        # Stage files
        if files:
            # Stage specific files
            for file_path in files:
                if not Path(file_path).exists():
                    result["warnings"].append(f"File not found: {file_path}")
                    continue

                add_result = await execute_git_command(["git", "add", file_path])
                if add_result["success"]:
                    result["files_committed"].append(file_path)
                else:
                    result["warnings"].append(f"Failed to stage: {file_path}")
        else:
            # Stage all changes
            add_result = await execute_git_command(["git", "add", "."])
            if add_result["success"]:
                # Get list of staged files
                staged_result = await execute_git_command(["git", "diff", "--cached", "--name-only"])
                if staged_result["success"]:
                    result["files_committed"] = staged_result["output"].strip().splitlines()

        # Validate commit message
        message_issues = _validate_commit_message(message)
        if message_issues:
            result["warnings"].extend(message_issues)

        # Create commit
        commit_cmd = ["git", "commit", "-m", message]
        if amend:
            commit_cmd.append("--amend")

        commit_result = await execute_git_command(commit_cmd)

        if commit_result["success"]:
            result["success"] = True

            # Extract commit hash
            hash_match = re.search(r'\[[\w\-_/]+\s+([a-f0-9]+)\]', commit_result["output"])
            if hash_match:
                result["commit_hash"] = hash_match.group(1)

            # Get commit stats
            stats_result = await execute_git_command(["git", "show", "--stat", "--format="])
            if stats_result["success"]:
                result["stats"] = _parse_commit_stats(stats_result["output"])

        else:
            result["message"] = f"Commit failed: {commit_result['error']}"

    except Exception as e:
        result["message"] = f"Error creating commit: {str(e)}"

    return result

async def handle_merges(source_branch: str, target_branch: str,
                       strategy: str = "merge") -> Dict[str, Any]:
    """
    Handle git merges with conflict detection and resolution guidance.

    Args:
        source_branch: Branch to merge from
        target_branch: Branch to merge into
        strategy: Merge strategy ("merge", "rebase", "squash")

    Returns:
        Merge operation result
    """
    result = {
        "success": False,
        "source_branch": source_branch,
        "target_branch": target_branch,
        "strategy": strategy,
        "conflicts": [],
        "message": "",
        "warnings": []
    }

    try:
        # Check if branches exist
        for branch in [source_branch, target_branch]:
            branch_check = await execute_git_command(["git", "branch", "--list", branch])
            if not branch_check["success"] or not branch_check["output"].strip():
                result["message"] = f"Branch does not exist: {branch}"
                return result

        # Switch to target branch
        checkout_result = await execute_git_command(["git", "checkout", target_branch])
        if not checkout_result["success"]:
            result["message"] = f"Failed to checkout target branch: {target_branch}"
            return result

        # Check for uncommitted changes
        status = await check_git_status()
        if status.get("uncommitted_changes", 0) > 0:
            result["message"] = "Uncommitted changes in working directory"
            return result

        # Perform merge based on strategy
        if strategy == "merge":
            merge_result = await execute_git_command(["git", "merge", source_branch])
        elif strategy == "rebase":
            merge_result = await execute_git_command(["git", "rebase", source_branch])
        elif strategy == "squash":
            merge_result = await execute_git_command(["git", "merge", "--squash", source_branch])
        else:
            result["message"] = f"Unknown merge strategy: {strategy}"
            return result

        if merge_result["success"]:
            result["success"] = True
            result["message"] = f"Successfully merged {source_branch} into {target_branch}"
        else:
            # Check for merge conflicts
            if "conflict" in merge_result["error"].lower():
                conflicts = await _detect_merge_conflicts()
                result["conflicts"] = conflicts
                result["message"] = f"Merge conflicts detected in {len(conflicts)} files"
                result["warnings"].append("Resolve conflicts manually before continuing")
            else:
                result["message"] = f"Merge failed: {merge_result['error']}"

    except Exception as e:
        result["message"] = f"Error handling merge: {str(e)}"

    return result

async def check_git_status() -> Dict[str, Any]:
    """
    Get comprehensive git repository status.

    Returns:
        Repository status information
    """
    status = {
        "current_branch": "",
        "uncommitted_changes": 0,
        "untracked_files": 0,
        "staged_files": 0,
        "unpushed_commits": 0,
        "behind_remote": 0,
        "ahead_remote": 0,
        "clean": True,
        "remote_exists": False,
        "last_commit": "",
        "repository_root": ""
    }

    try:
        # Get current branch
        branch_result = await execute_git_command(["git", "branch", "--show-current"])
        if branch_result["success"]:
            status["current_branch"] = branch_result["output"].strip()

        # Get repository root
        root_result = await execute_git_command(["git", "rev-parse", "--show-toplevel"])
        if root_result["success"]:
            status["repository_root"] = root_result["output"].strip()

        # Get status information
        status_result = await execute_git_command(["git", "status", "--porcelain"])
        if status_result["success"]:
            status_lines = status_result["output"].splitlines()

            for line in status_lines:
                if line.startswith(' M') or line.startswith(' D'):
                    status["uncommitted_changes"] += 1
                elif line.startswith('??'):
                    status["untracked_files"] += 1
                elif line.startswith('M ') or line.startswith('A ') or line.startswith('D '):
                    status["staged_files"] += 1

        # Check remote status
        remote_result = await execute_git_command(["git", "remote"])
        if remote_result["success"] and remote_result["output"].strip():
            status["remote_exists"] = True

            # Check ahead/behind status
            if status["current_branch"]:
                ahead_behind_result = await execute_git_command([
                    "git", "rev-list", "--left-right", "--count",
                    f"origin/{status['current_branch']}...HEAD"
                ])
                if ahead_behind_result["success"]:
                    parts = ahead_behind_result["output"].strip().split()
                    if len(parts) == 2:
                        status["behind_remote"] = int(parts[0])
                        status["ahead_remote"] = int(parts[1])
                        status["unpushed_commits"] = status["ahead_remote"]

        # Get last commit
        last_commit_result = await execute_git_command([
            "git", "log", "-1", "--format=%h %s (%cr)"
        ])
        if last_commit_result["success"]:
            status["last_commit"] = last_commit_result["output"].strip()

        # Determine if repository is clean
        status["clean"] = (
            status["uncommitted_changes"] == 0 and
            status["untracked_files"] == 0 and
            status["staged_files"] == 0
        )

    except Exception as e:
        status["error"] = str(e)

    return status

async def execute_git_command(command: List[str], timeout: int = 30) -> Dict[str, Any]:
    """
    Execute git command with proper error handling and timeout.

    Args:
        command: Git command as list of strings
        timeout: Command timeout in seconds

    Returns:
        Command execution result
    """
    result = {
        "success": False,
        "output": "",
        "error": "",
        "return_code": -1,
        "command": " ".join(command)
    }

    try:
        process = await asyncio.create_subprocess_exec(
            *command,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            cwd=None  # Use current directory
        )

        stdout, stderr = await asyncio.wait_for(
            process.communicate(),
            timeout=timeout
        )

        result["return_code"] = process.returncode
        result["output"] = stdout.decode('utf-8', errors='replace')
        result["error"] = stderr.decode('utf-8', errors='replace')
        result["success"] = process.returncode == 0

    except asyncio.TimeoutError:
        result["error"] = f"Command timed out after {timeout} seconds"
    except Exception as e:
        result["error"] = f"Command execution error: {str(e)}"

    return result

# Helper functions

def _is_valid_branch_name(branch_name: str) -> bool:
    """Validate branch name according to Agent OS conventions."""
    # No dates at the start
    if re.match(r'^\d{4}-\d{2}-\d{2}', branch_name):
        return False

    # Must be kebab-case
    if not re.match(r'^[a-z0-9\-]+$', branch_name):
        return False

    # Reasonable length
    if len(branch_name) < 3 or len(branch_name) > 50:
        return False

    return True

def _validate_commit_message(message: str) -> List[str]:
    """Validate commit message quality."""
    issues = []

    if len(message) < 10:
        issues.append("Commit message too short (minimum 10 characters)")

    if len(message) > 72:
        issues.append("Commit message too long (maximum 72 characters for first line)")

    if not message[0].isupper():
        issues.append("Commit message should start with capital letter")

    if message.endswith('.'):
        issues.append("Commit message should not end with period")

    # Check for meaningful content
    generic_words = ['update', 'fix', 'change', 'modify']
    if any(word in message.lower() for word in generic_words) and len(message.split()) < 4:
        issues.append("Commit message should be more descriptive")

    return issues

def _parse_commit_stats(stats_output: str) -> Dict[str, Any]:
    """Parse git commit statistics."""
    stats = {
        "files_changed": 0,
        "insertions": 0,
        "deletions": 0
    }

    # Parse format: "X files changed, Y insertions(+), Z deletions(-)"
    match = re.search(r'(\d+) files? changed', stats_output)
    if match:
        stats["files_changed"] = int(match.group(1))

    match = re.search(r'(\d+) insertions?\(\+\)', stats_output)
    if match:
        stats["insertions"] = int(match.group(1))

    match = re.search(r'(\d+) deletions?\(\-\)', stats_output)
    if match:
        stats["deletions"] = int(match.group(1))

    return stats

async def _detect_merge_conflicts() -> List[Dict[str, Any]]:
    """Detect files with merge conflicts."""
    conflicts = []

    # Get files with conflicts
    conflict_result = await execute_git_command(["git", "diff", "--name-only", "--diff-filter=U"])

    if conflict_result["success"]:
        for file_path in conflict_result["output"].strip().splitlines():
            if file_path:
                conflicts.append({
                    "file": file_path,
                    "type": "merge_conflict",
                    "status": "unresolved"
                })

    return conflicts