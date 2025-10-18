# Code Hound MCP Server

MCP server for static analysis, TDD/SOLID/DRY enforcement, and quality metrics.

## Features

**MVP (Tier 1):**
- `comprehensive_code_review`: Full code review using ruff, mypy, bandit
- `enforce_coding_standards`: TDD/SOLID/DRY/KISS enforcement
- `detect_code_smells`: Anti-pattern detection

**Tier 2 (Planned):**
- `project_quality_audit`: Project-wide quality audit
- `calculate_complexity_metrics`: Cyclomatic complexity
- `get_synapse_patterns`: Synapse-specific patterns

## Installation

```bash
cd /home/m0xu/1-projects/synapse/.synapse/agents/code-hound
/home/m0xu/1-projects/synapse/.venv/bin/python -m pip install -e .

# Optional: Install linters for full functionality
/home/m0xu/1-projects/synapse/.venv/bin/python -m pip install ruff mypy bandit
```

## Usage

### Standalone Testing

```bash
# Start MCP server (stdio mode)
/home/m0xu/1-projects/synapse/.venv/bin/python -m server
```

### Via Claude Code

```python
# Comprehensive code review
review = mcp__code_hound__comprehensive_code_review(
    file_path="/path/to/module.py",
    language="python",
    review_type="full"  # or "quick", "security"
)

# Enforce coding standards
report = mcp__code_hound__enforce_coding_standards(
    file_path="/path/to/project",
    standards=["TDD", "SOLID", "DRY"]
)

# Detect code smells
smells = mcp__code_hound__detect_code_smells(
    file_path="/path/to/module.py",
    language="python"
)
```

## Architecture

```
Claude Code
    ↓ MCP Protocol (JSON-RPC over stdio)
Code Hound Server
    ↓ subprocess
ruff / mypy / bandit
    ↓
Analysis Results
```

## Supported Languages

**Python (Full Support):**
- ruff (linting, code style)
- mypy (type checking)
- bandit (security)

**Other Languages (Planned):**
- Rust: clippy, cargo check
- TypeScript: eslint, tsc
- Go: golint, go vet

## Version

1.0.0 (MVP release)
