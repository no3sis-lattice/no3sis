"""
Configuration Management

Manage Code Hound's configuration including quality thresholds, enforcement rules,
and model selection preferences.
"""

import yaml
import os
from pathlib import Path
from typing import Dict, Any, Optional, List

# Default configuration
DEFAULT_CONFIG = {
    "agent": {
        "name": "code-hound",
        "version": "1.0.0",
        "model_preference": {
            "primary": "claude-3-opus",
            "fallback": "claude-3-sonnet",
            "simple_tasks": "claude-3-haiku"
        },
        "complexity_routing": {
            "high_complexity": "opus",
            "medium_complexity": "sonnet",
            "low_complexity": "haiku"
        },
        "cost_optimization": {
            "prefer_cheaper": False,  # Code Hound prioritizes quality over cost
            "fallback_on_rate_limit": True,
            "budget_cap_per_hour": 200
        }
    },
    "quality_thresholds": {
        "overall_minimum": 70,
        "tdd_minimum": 60,
        "solid_minimum": 65,
        "dry_minimum": 75,
        "kiss_minimum": 70,
        "no_shortcuts_minimum": 80
    },
    "enforcement_rules": {
        "block_on_critical": True,
        "require_tests": True,
        "max_complexity": 10,
        "max_function_length": 20,
        "max_nesting_depth": 4,
        "zero_tolerance_shortcuts": True
    },
    "language_specific": {
        "python": {
            "max_complexity": 10,
            "max_function_length": 20,
            "max_line_length": 88,
            "require_type_hints": True,
            "pep8_compliance": True
        },
        "javascript": {
            "max_complexity": 8,
            "max_function_length": 15,
            "max_line_length": 100,
            "require_strict_mode": True
        },
        "typescript": {
            "max_complexity": 8,
            "max_function_length": 15,
            "max_line_length": 100,
            "require_strict_null_checks": True
        },
        "rust": {
            "max_complexity": 12,
            "max_function_length": 25,
            "clippy_pedantic": True,
            "no_unsafe_unless_justified": True
        },
        "go": {
            "max_complexity": 10,
            "max_function_length": 20,
            "gofmt_compliance": True
        }
    },
    "reporting": {
        "format": "markdown",
        "include_metrics": True,
        "show_progress": True,
        "verbose_violations": True
    },
    "integrations": {
        "synapse_enabled": True,
        "git_hooks": False,
        "ci_integration": False
    },
    "catchphrases": [
        "This shortcut stops here. Fix it properly or don't ship it.",
        "I smell technical debt. Time to pay it off.",
        "Where are the tests? No tests, no merge.",
        "Complexity is the enemy. Simplify or justify.",
        "This violates SOLID principles. Refactor required.",
        "Copy-paste detected. Extract and reuse.",
        "Good code tells a story. This is gibberish."
    ]
}

def load_config(config_path: Optional[str] = None) -> Dict[str, Any]:
    """
    Load Code Hound configuration from file or use defaults.

    Args:
        config_path: Optional path to config file

    Returns:
        Configuration dictionary
    """
    if config_path is None:
        # Look for config in standard locations
        possible_paths = [
            Path(__file__).parent.parent / "code_hound_config.yml",
            Path.cwd() / ".code_hound.yml",
            Path.home() / ".code_hound.yml"
        ]

        for path in possible_paths:
            if path.exists():
                config_path = str(path)
                break

    if config_path and Path(config_path).exists():
        try:
            with open(config_path, 'r') as f:
                user_config = yaml.safe_load(f)

            # Merge with defaults
            config = _deep_merge(DEFAULT_CONFIG, user_config)
            return config
        except Exception as e:
            print(f"⚠️ Error loading config from {config_path}: {e}")
            print("Using default configuration")

    return DEFAULT_CONFIG.copy()

def save_config(config: Dict[str, Any], config_path: Optional[str] = None) -> bool:
    """
    Save configuration to file.

    Args:
        config: Configuration to save
        config_path: Optional path to save to

    Returns:
        Success status
    """
    if config_path is None:
        config_path = Path(__file__).parent.parent / "code_hound_config.yml"

    try:
        with open(config_path, 'w') as f:
            yaml.dump(config, f, default_flow_style=False, indent=2)
        return True
    except Exception as e:
        print(f"⚠️ Error saving config to {config_path}: {e}")
        return False

def get_quality_thresholds(config: Optional[Dict[str, Any]] = None) -> Dict[str, int]:
    """
    Get quality thresholds from configuration.

    Args:
        config: Optional configuration dictionary

    Returns:
        Quality thresholds
    """
    if config is None:
        config = load_config()

    return config.get("quality_thresholds", DEFAULT_CONFIG["quality_thresholds"])

def get_enforcement_rules(config: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Get enforcement rules from configuration.

    Args:
        config: Optional configuration dictionary

    Returns:
        Enforcement rules
    """
    if config is None:
        config = load_config()

    return config.get("enforcement_rules", DEFAULT_CONFIG["enforcement_rules"])

def get_language_config(language: str, config: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Get language-specific configuration.

    Args:
        language: Programming language
        config: Optional configuration dictionary

    Returns:
        Language-specific configuration
    """
    if config is None:
        config = load_config()

    language_configs = config.get("language_specific", DEFAULT_CONFIG["language_specific"])
    return language_configs.get(language.lower(), {})

def should_block_on_violation(violation_severity: str, config: Optional[Dict[str, Any]] = None) -> bool:
    """
    Determine if Code Hound should block on a violation.

    Args:
        violation_severity: Severity level (critical, major, medium, low)
        config: Optional configuration dictionary

    Returns:
        Whether to block
    """
    if config is None:
        config = load_config()

    rules = get_enforcement_rules(config)

    if violation_severity == "critical":
        return rules.get("block_on_critical", True)
    elif violation_severity == "major":
        return rules.get("block_on_major", False)

    return False

def get_model_for_complexity(complexity_level: str, config: Optional[Dict[str, Any]] = None) -> str:
    """
    Get appropriate model for complexity level.

    Args:
        complexity_level: high, medium, or low
        config: Optional configuration dictionary

    Returns:
        Model name to use
    """
    if config is None:
        config = load_config()

    agent_config = config.get("agent", {})
    routing = agent_config.get("complexity_routing", {})

    model_short = routing.get(f"{complexity_level}_complexity", "sonnet")

    # Map short names to full model names
    model_map = {
        "haiku": "claude-3-haiku",
        "sonnet": "claude-3-sonnet",
        "opus": "claude-3-opus"
    }

    return model_map.get(model_short, "claude-3-sonnet")

def get_random_catchphrase(config: Optional[Dict[str, Any]] = None) -> str:
    """
    Get a random Code Hound catchphrase.

    Args:
        config: Optional configuration dictionary

    Returns:
        Random catchphrase
    """
    import random

    if config is None:
        config = load_config()

    catchphrases = config.get("catchphrases", DEFAULT_CONFIG["catchphrases"])
    return random.choice(catchphrases)

def is_feature_enabled(feature_name: str, config: Optional[Dict[str, Any]] = None) -> bool:
    """
    Check if a feature is enabled.

    Args:
        feature_name: Name of feature to check
        config: Optional configuration dictionary

    Returns:
        Whether feature is enabled
    """
    if config is None:
        config = load_config()

    integrations = config.get("integrations", {})
    return integrations.get(feature_name, False)

def update_config_value(key_path: str, value: Any, config_path: Optional[str] = None) -> bool:
    """
    Update a specific configuration value.

    Args:
        key_path: Dot-separated path to config key (e.g., "quality_thresholds.tdd_minimum")
        value: New value
        config_path: Optional config file path

    Returns:
        Success status
    """
    config = load_config(config_path)

    # Navigate to the right location
    keys = key_path.split('.')
    current = config

    for key in keys[:-1]:
        if key not in current:
            current[key] = {}
        current = current[key]

    # Set the value
    current[keys[-1]] = value

    return save_config(config, config_path)

def validate_config(config: Dict[str, Any]) -> List[str]:
    """
    Validate configuration for common issues.

    Args:
        config: Configuration to validate

    Returns:
        List of validation errors
    """
    errors = []

    # Check required sections
    required_sections = ["agent", "quality_thresholds", "enforcement_rules"]
    for section in required_sections:
        if section not in config:
            errors.append(f"Missing required section: {section}")

    # Check threshold ranges
    if "quality_thresholds" in config:
        thresholds = config["quality_thresholds"]
        for key, value in thresholds.items():
            if not isinstance(value, int) or not 0 <= value <= 100:
                errors.append(f"Invalid threshold {key}: must be integer 0-100")

    # Check model names
    if "agent" in config and "model_preference" in config["agent"]:
        models = config["agent"]["model_preference"]
        valid_models = ["claude-3-haiku", "claude-3-sonnet", "claude-3-opus"]
        for key, model in models.items():
            if model not in valid_models:
                errors.append(f"Invalid model {model} for {key}")

    return errors

def _deep_merge(base: Dict[str, Any], update: Dict[str, Any]) -> Dict[str, Any]:
    """Deep merge two dictionaries."""
    result = base.copy()

    for key, value in update.items():
        if key in result and isinstance(result[key], dict) and isinstance(value, dict):
            result[key] = _deep_merge(result[key], value)
        else:
            result[key] = value

    return result

# Environment variable overrides
def apply_env_overrides(config: Dict[str, Any]) -> Dict[str, Any]:
    """Apply environment variable overrides to config."""
    env_mappings = {
        "CODE_HOUND_MODEL": "agent.model_preference.primary",
        "CODE_HOUND_BLOCK_CRITICAL": "enforcement_rules.block_on_critical",
        "CODE_HOUND_MIN_SCORE": "quality_thresholds.overall_minimum",
        "CODE_HOUND_BUDGET": "agent.cost_optimization.budget_cap_per_hour"
    }

    for env_var, config_path in env_mappings.items():
        if env_var in os.environ:
            value = os.environ[env_var]

            # Convert string values to appropriate types
            if value.lower() in ("true", "false"):
                value = value.lower() == "true"
            elif value.isdigit():
                value = int(value)

            keys = config_path.split('.')
            current = config
            for key in keys[:-1]:
                if key not in current:
                    current[key] = {}
                current = current[key]
            current[keys[-1]] = value

    return config