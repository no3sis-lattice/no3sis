"""Configuration Management for Architect"""

import yaml
from pathlib import Path
from typing import Dict, Any, Optional

DEFAULT_CONFIG = {
    "agent": {
        "name": "architect",
        "version": "1.0.0",
        "model_preference": {
            "primary": "claude-3-opus",
            "fallback": "claude-3-sonnet"
        }
    },
    "architectural_standards": {
        "preferred_patterns": ["microservices", "event-driven"],
        "documentation_format": "c4",
        "decision_tracking": True
    }
}

def load_config(config_path: Optional[str] = None) -> Dict[str, Any]:
    if config_path and Path(config_path).exists():
        try:
            with open(config_path, 'r') as f:
                return {**DEFAULT_CONFIG, **yaml.safe_load(f)}
        except Exception:
            pass
    return DEFAULT_CONFIG.copy()

def get_architectural_standards() -> Dict[str, Any]:
    return DEFAULT_CONFIG["architectural_standards"]

def get_design_preferences() -> Dict[str, Any]:
    return {"documentation": "comprehensive", "patterns": "proven"}