#!/bin/bash
# Claude Code Setup - Now Simplified!
# Usage: setup-claude-code [project-directory]

echo "🎯 Claude Code + Synapse Setup"
echo "==============================="
echo
echo "The setup has been greatly simplified!"
echo
echo "Just run: no3sis init ."
echo

# Delegate to the new simple system
if [[ -n "$1" ]]; then
    exec ~/.no3sis-system/bin/no3sis init "$1"
else
    exec ~/.no3sis-system/bin/no3sis init .
fi