"""
Configuration Management for Git Workflow

Manage git workflow configuration, conventions, and branch rules.
"""

import yaml
from pathlib import Path
from typing import Dict, Any, Optional

DEFAULT_CONFIG = {
    "agent": {
        "name": "git-workflow",
        "version": "1.0.0",
        "model_preference": {
            "primary": "claude-3-sonnet",
            "fallback": "claude-3-haiku",
            "simple_tasks": "claude-3-haiku"
        }
    },
    "git_conventions": {
        "commit_format": "conventional",
        "branch_naming": "kebab-case",
        "default_target_branch": "main",
        "require_pr": True
    },
    "workflow_rules": {
        "auto_push": True,
        "create_pr_on_completion": True,
        "cleanup_branches": False,
        "require_tests": True
    }
}

def load_config(config_path: Optional[str] = None) -> Dict[str, Any]:
    """Load configuration from file or use defaults."""
    if config_path and Path(config_path).exists():
        try:
            with open(config_path, 'r') as f:
                user_config = yaml.safe_load(f)
            # Merge with defaults
            config = {**DEFAULT_CONFIG, **user_config}
            return config
        except Exception:
            pass

    return DEFAULT_CONFIG.copy()

def get_git_conventions(config: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Get git conventions from configuration."""
    if config is None:
        config = load_config()
    return config.get("git_conventions", DEFAULT_CONFIG["git_conventions"])

def get_branch_rules(config: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Get branch management rules."""
    if config is None:
        config = load_config()
    return config.get("workflow_rules", DEFAULT_CONFIG["workflow_rules"])