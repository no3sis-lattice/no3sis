# File Creator MCP Server

MCP server for complex file operations with pattern learning capabilities.

## Features

**MVP (Tier 1):**
- `create_single_file`: Create individual files with optional template application
- `create_directory_structure`: Create nested directory structures
- `batch_create_files`: Create multiple files efficiently

**Tier 2 (Planned):**
- `apply_file_template`: Template rendering with variable substitution
- `search_file_templates`: Template discovery
- `get_template_info`: Template metadata
- `query_synapse_templates`: Synapse-specific templates

## Installation

```bash
cd /home/m0xu/1-projects/synapse/.synapse/agents/file-creator
/home/m0xu/1-projects/synapse/.venv/bin/python -m pip install -e .
```

## Usage

### Standalone Testing

```bash
# Start MCP server (stdio mode)
/home/m0xu/1-projects/synapse/.venv/bin/python -m server
```

### Via Claude Code

```python
# Create single file
result = mcp__file_creator__create_single_file(
    file_path="/path/to/file.py",
    content="print('Hello, world!')"
)

# Create directory structure
result = mcp__file_creator__create_directory_structure(
    base_path="/path/to/project",
    structure={
        "src": {
            "__init__.py": "",
            "main.py": "# Entry point"
        },
        "tests": {
            "test_main.py": "# Tests"
        }
    }
)

# Batch create files
result = mcp__file_creator__batch_create_files([
    {"file_path": "file1.py", "content": "..."},
    {"file_path": "file2.py", "content": "..."}
])
```

## Architecture

```
Claude Code
    ↓ MCP Protocol (JSON-RPC over stdio)
File Creator Server
    ↓ Python pathlib
Filesystem
```

## Version

1.0.0 (MVP release)
