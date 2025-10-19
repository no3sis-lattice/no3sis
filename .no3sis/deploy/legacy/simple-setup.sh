#!/bin/bash
# Simple Claude Code Setup for Synapse
# ====================================

set -e

SYNAPSE_ROOT="$HOME/.synapse-system/.synapse"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

log() { echo -e "${BLUE}[SETUP]${NC} $1"; }
success() { echo -e "${GREEN}✓${NC} $1"; }
info() { echo -e "${CYAN}ℹ${NC} $1"; }

# Detect language
detect_language() {
    local dir="$1"
    if [[ -f "$dir/Cargo.toml" ]]; then echo "rust"
    elif [[ -f "$dir/go.mod" ]]; then echo "golang"
    elif [[ -f "$dir/package.json" ]]; then echo "typescript"
    elif [[ -f "$dir/build.zig" ]]; then echo "zig"
    elif [[ -f "$dir/Makefile" ]]; then echo "c"
    else echo "unknown"; fi
}

# Main setup
setup() {
    local project_dir="${1:-.}"
    local language="${2:-$(detect_language "$project_dir")}"
    local description="$3"

    project_dir="$(realpath "$project_dir")"

    if [[ "$language" == "unknown" ]]; then
        echo "Could not detect language. Specify with: $0 . rust"
        exit 1
    fi

    log "Setting up $language project: $(basename "$project_dir")"

    # Initialize synapse
    if [[ ! -d "$project_dir/.synapse" ]]; then
        log "Initializing synapse..."
        "$SYNAPSE_ROOT/deploy/init-project.sh" --language "$language" --project "$project_dir"
    fi

    # Setup Claude Code directory
    log "Setting up Claude Code agents..."
    mkdir -p "$project_dir/.claude-code/agents"

    # Copy project manager
    cp "$SYNAPSE_ROOT/tools/synapse-project-manager.md" "$project_dir/.claude-code/agents/"

    # Create simple project context
    cat > "$project_dir/.claude-code/PROJECT_CONTEXT.md" << EOF
# Project Context

- **Language**: $language
- **Description**: ${description:-"$language project"}
- **Synapse**: Available at .synapse/
- **Setup**: $(date)

## Available Agents

- synapse-project-manager.md - Project management with synapse integration

## Quick Commands

\`\`\`bash
# Search synapse knowledge (if local synapse exists)
cd .synapse && python search.py "your query"

# Search global synapse knowledge
cd ~/.synapse-system/.synapse/neo4j && source .venv/bin/activate && python synapse_search.py "your query"

# Check synapse health
cd ~/.synapse-system/.synapse/neo4j && source .venv/bin/activate && python context_manager.py --health
\`\`\`

## Usage

\`\`\`
@claude-code/agents/synapse-project-manager.md help me with this $language project
\`\`\`
EOF

    success "Setup complete!"
    echo
    info "Your $language project is ready for Claude Code!"
    info "Available agent: @claude-code/agents/synapse-project-manager.md"
    info "Project context: .claude-code/PROJECT_CONTEXT.md"
    echo
    info "Try: @claude-code/agents/synapse-project-manager.md analyze this project"
}

setup "$@"