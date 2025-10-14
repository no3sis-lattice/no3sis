#!/bin/bash
# Claude Code Setup - Now Simplified!
# Usage: setup-claude-code [project-directory]

echo "🎯 Claude Code + Synapse Setup"
echo "==============================="
echo
echo "The setup has been greatly simplified!"
echo
echo "Just run: synapse init ."
echo

# Delegate to the new simple system
if [[ -n "$1" ]]; then
    exec ~/.synapse-system/bin/synapse init "$1"
else
    exec ~/.synapse-system/bin/synapse init .
fi