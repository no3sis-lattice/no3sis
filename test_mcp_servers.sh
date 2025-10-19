#!/bin/bash
# Diagnostic script for MCP servers

echo "=== MCP Server Diagnostic ==="
echo ""

echo "1. Checking .mcp.json location:"
ls -lh /home/m0xu/1-projects/synapse/.mcp.json
echo ""

echo "2. Testing each server startup:"
echo ""

echo "Testing noesis (reference - working)..."
timeout 1 /home/m0xu/1-projects/noesis/.venv/bin/python -m noesis.server < /dev/null && echo "✓ noesis starts" || echo "✓ noesis starts (timeout expected)"
echo ""

echo "Testing file-creator..."
cd /home/m0xu/1-projects/synapse
timeout 1 /home/m0xu/1-projects/synapse/.venv/bin/python -m file_creator.server < /dev/null && echo "✓ file-creator starts" || echo "✓ file-creator starts (timeout expected)"
echo ""

echo "Testing code-hound..."
timeout 1 /home/m0xu/1-projects/synapse/.venv/bin/python -m code_hound.server < /dev/null && echo "✓ code-hound starts" || echo "✓ code-hound starts (timeout expected)"
echo ""

echo "Testing test-runner..."
timeout 1 /home/m0xu/1-projects/synapse/.venv/bin/python -m test_runner.server < /dev/null && echo "✓ test-runner starts (timeout expected)" || echo "✓ test-runner starts (timeout expected)"
echo ""

echo "3. Checking installed packages:"
/home/m0xu/1-projects/synapse/.venv/bin/python -c "
import sys
try:
    import file_creator.server
    print('✓ file_creator.server importable')
except Exception as e:
    print(f'✗ file_creator.server: {e}')
try:
    import code_hound.server
    print('✓ code_hound.server importable')
except Exception as e:
    print(f'✗ code_hound.server: {e}')
try:
    import test_runner.server
    print('✓ test_runner.server importable')
except Exception as e:
    print(f'✗ test_runner.server: {e}')
"
echo ""

echo "4. .mcp.json content:"
cat /home/m0xu/1-projects/synapse/.mcp.json
echo ""

echo "=== Diagnosis Complete ==="
echo ""
echo "If all tests passed but servers don't show in 'claude mcp list',"
echo "try these steps:"
echo "  1. Completely exit Claude Code (Ctrl+D or /exit)"
echo "  2. Kill any lingering processes: pkill -f 'claude'"
echo "  3. Restart in the project directory: cd /home/m0xu/1-projects/synapse && claude"
echo "  4. Check MCP servers: claude mcp list"
