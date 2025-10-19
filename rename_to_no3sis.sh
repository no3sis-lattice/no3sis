#!/usr/bin/env bash
# Systematic rename from synapse/no3sis → no3sis
# Generated 2025-10-19

set -euo pipefail

echo "🔄 Starting systematic rename: synapse/no3sis → no3sis"

# Function to replace in file
replace_in_file() {
    local file="$1"
    local old="$2"
    local new="$3"

    if [[ -f "$file" ]]; then
        sed -i "s|${old}|${new}|g" "$file"
    fi
}

# Phase 1: Critical config files
echo "📝 Phase 1: Updating configuration files..."

# .mcp.json - Update paths
replace_in_file ".mcp.json" "/home/m0xu/1-projects/synapse" "/home/m0xu/1-projects/no3sis"

# pyproject.toml
if [[ -f "pyproject.toml" ]]; then
    sed -i 's/name = "synapse"/name = "no3sis"/g' pyproject.toml
    sed -i 's/synapse\./no3sis./g' pyproject.toml
fi

# .synapse.yml → .no3sis.yml
if [[ -f ".synapse.yml" ]]; then
    git mv .synapse.yml .no3sis.yml 2>/dev/null || mv .synapse.yml .no3sis.yml
fi

# Phase 2: Python imports and module names
echo "🐍 Phase 2: Updating Python imports..."

find . -name "*.py" -type f ! -path "./.venv/*" ! -path "./build/*" ! -path "./.git/*" -exec sed -i \
    -e 's/from synapse\./from no3sis./g' \
    -e 's/import synapse/import no3sis/g' \
    -e 's/synapse\./no3sis./g' \
    -e "s|\.synapse|\.no3sis|g" \
    {} +

# Phase 3: Documentation files
echo "📚 Phase 3: Updating documentation..."

# LOGOS.md, README.md, CHANGELOG.md
for doc in LOGOS.md README.md CHANGELOG.md CLAUDE.md; do
    if [[ -f "$doc" ]]; then
        sed -i \
            -e 's/Synapse System/No3sis System/g' \
            -e 's/Synapse:/No3sis:/g' \
            -e 's/synapse/no3sis/g' \
            -e 's/Synapse/No3sis/g' \
            -e "s|\.synapse|\.no3sis|g" \
            "$doc"
    fi
done

# Phase 4: Nix flakes
echo "❄️  Phase 4: Updating Nix configurations..."

find nix/flakes -name "flake.nix" -type f -exec sed -i \
    -e 's/synapse-system/no3sis-system/g' \
    -e 's/synapse-core/no3sis-core/g' \
    -e 's|synapse/|no3sis/|g' \
    -e "s|\.synapse|\.no3sis|g" \
    {} +

# Main flake.nix
if [[ -f "flake.nix" ]]; then
    sed -i \
        -e 's/synapse-system/no3sis-system/g' \
        -e 's/description = "Synapse/description = "No3sis/g' \
        -e "s|\.synapse|\.no3sis|g" \
        flake.nix
fi

# Phase 5: CI/CD workflows
echo "⚙️  Phase 5: Updating CI/CD workflows..."

find .github/workflows -name "*.yml" -type f -exec sed -i \
    -e 's/synapse/no3sis/g' \
    -e "s|\.synapse|\.no3sis|g" \
    {} + 2>/dev/null || true

# Phase 6: Scripts
echo "🔧 Phase 6: Updating scripts..."

find scripts -name "*.py" -o -name "*.sh" -type f 2>/dev/null | while read -r script; do
    sed -i \
        -e 's/synapse/no3sis/g' \
        -e "s|\.synapse|\.no3sis|g" \
        "$script" 2>/dev/null || true
done

# Phase 7: MCP server files in .no3sis/agents
echo "🤖 Phase 7: Updating MCP agent files..."

find .no3sis/agents -name "*.py" -type f -exec sed -i \
    -e 's/synapse_integration/no3sis_integration/g' \
    -e 's/from synapse/from no3sis/g' \
    -e 's/import synapse/import no3sis/g' \
    {} +

# Rename synapse_integration.py files
find .no3sis/agents -name "synapse_integration.py" -type f | while read -r file; do
    newfile="${file/synapse_integration/no3sis_integration}"
    git mv "$file" "$newfile" 2>/dev/null || mv "$file" "$newfile"
done

# Phase 8: MCP server source code
echo "🔌 Phase 8: Updating MCP server source..."

if [[ -d ".no3sis/agents/code-hound/src/code_hound" ]]; then
    find .no3sis/agents/code-hound/src -name "*.py" -exec sed -i 's/Synapse/No3sis/g' {} +
fi

if [[ -d ".no3sis/agents/file-creator/src/file_creator" ]]; then
    find .no3sis/agents/file-creator/src -name "*.py" -exec sed -i 's/Synapse/No3sis/g' {} +
fi

# Phase 9: Package names in MCP server pyproject.toml
echo "📦 Phase 9: Updating MCP package names..."

find .no3sis/agents -name "pyproject.toml" -type f -exec sed -i \
    -e 's/synapse/no3sis/g' \
    -e 's/Synapse/No3sis/g' \
    {} +

# Phase 10: Neo4j and tools
echo "🗄️  Phase 10: Updating Neo4j and tool files..."

if [[ -d ".no3sis/neo4j" ]]; then
    find .no3sis/neo4j -name "synapse_*.py" | while read -r file; do
        newfile="${file/synapse_/no3sis_}"
        git mv "$file" "$newfile" 2>/dev/null || mv "$file" "$newfile"
    done

    find .no3sis/neo4j -name "*.py" -type f -exec sed -i 's/synapse/no3sis/g' {} +
fi

if [[ -f ".no3sis/tools/synapse_tools.py" ]]; then
    git mv .no3sis/tools/synapse_tools.py .no3sis/tools/no3sis_tools.py 2>/dev/null || \
        mv .no3sis/tools/synapse_tools.py .no3sis/tools/no3sis_tools.py
fi

echo "✅ Rename complete! Next steps:"
echo "1. Review changes: git status"
echo "2. Test MCP servers"
echo "3. Update virtual environment location if needed"
echo "4. Commit changes"
