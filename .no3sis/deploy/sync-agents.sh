#!/bin/bash

# This script syncs the agent definitions from the master .synapse/agents directory
# to the .claude/agents directory for use by Claude.

SYNAPSE_AGENTS_DIR=~/.synapse-system/.synapse/agents
CLAUDE_AGENTS_DIR=~/.synapse-system/.claude/agents

# Check if source directory exists
if [[ ! -d "$SYNAPSE_AGENTS_DIR" ]]; then
    echo "Error: Source directory does not exist: $SYNAPSE_AGENTS_DIR"
    exit 1
fi

# Check if there are any .md files to sync
if ! ls "$SYNAPSE_AGENTS_DIR"/*.md >/dev/null 2>&1; then
    echo "Error: No agent .md files found in $SYNAPSE_AGENTS_DIR"
    exit 1
fi

# Create the .claude/agents directory if it doesn't exist
mkdir -p "$CLAUDE_AGENTS_DIR"

# Copy all agent definitions from .synapse/agents to .claude/agents
if cp -f "$SYNAPSE_AGENTS_DIR"/*.md "$CLAUDE_AGENTS_DIR"/; then
    echo "Agents synced successfully from $SYNAPSE_AGENTS_DIR to $CLAUDE_AGENTS_DIR"
    echo "Synced $(ls "$CLAUDE_AGENTS_DIR"/*.md 2>/dev/null | wc -l) agent files"
else
    echo "Error: Failed to sync agents"
    exit 1
fi
