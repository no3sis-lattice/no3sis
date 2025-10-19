# Test Runner MCP Server

MCP server for multi-framework test execution, failure analysis, and coverage reporting.

## Features

**MVP (Tier 1):**
- `execute_tests`: Run tests using pytest, jest, cargo, go
- `detect_test_framework`: Auto-detect test framework
- `analyze_test_failures`: Root cause analysis and fix suggestions

**Tier 2 (Planned):**
- `generate_coverage_report`: Coverage metrics
- `query_test_patterns`: Test pattern search
- `search_test_solutions`: Solution search for failures
- `run_test_suite`: Named test suite execution
- `extract_test_metadata`: Test metadata extraction

## Installation

```bash
cd /home/m0xu/1-projects/synapse/.synapse/agents/test-runner
/home/m0xu/1-projects/synapse/.venv/bin/python -m pip install -e .

# Optional: Install test frameworks
/home/m0xu/1-projects/synapse/.venv/bin/python -m pip install pytest pytest-cov
```

## Usage

### Standalone Testing

```bash
# Start MCP server (stdio mode)
/home/m0xu/1-projects/synapse/.venv/bin/python -m server
```

### Via Claude Code

```python
# Execute tests
result = mcp__test_runner__execute_tests(
    test_spec="tests/test_module.py",
    framework="pytest"  # auto-detected if omitted
)

# Detect framework
framework_info = mcp__test_runner__detect_test_framework(
    directory="/path/to/project"
)

# Analyze failures
analysis = mcp__test_runner__analyze_test_failures(
    failures=result["failures"],
    language="python"
)
```

## Architecture

```
Claude Code
    ↓ MCP Protocol (JSON-RPC over stdio)
Test Runner Server
    ↓ subprocess
pytest / jest / cargo test / go test
    ↓
Test Results + Analysis
```

## Supported Frameworks

- **pytest** (Python) - Full support
- **jest** (JavaScript/TypeScript) - Basic support
- **cargo test** (Rust) - Basic support
- **go test** (Go) - Basic support

## Failure Analysis

Detects common patterns:
- AssertionError (test logic issues)
- AttributeError (missing attributes)
- TypeError (type mismatches)
- ImportError (missing dependencies)
- FileNotFoundError (missing files)

Provides actionable suggestions for each pattern.

## Version

1.0.0 (MVP release)
