#!/bin/bash
# Claude Code Project Setup for Synapse System
# ============================================
#
# One-command setup to make any project Claude Code ready with language-specific synapse

set -e

# Configuration
SYNAPSE_ROOT="$HOME/.synapse-system/.synapse"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Logging functions
log() {
    echo -e "${BLUE}[CLAUDE-CODE-SETUP]${NC} $1"
}

success() {
    echo -e "${GREEN}✓${NC} $1"
}

warning() {
    echo -e "${YELLOW}⚠${NC} $1"
}

error() {
    echo -e "${RED}✗${NC} $1"
}

info() {
    echo -e "${CYAN}ℹ${NC} $1"
}

show_help() {
    cat << EOF
Claude Code Project Setup with Synapse Integration

USAGE:
    $0 [PROJECT_DIR] [OPTIONS]

ARGUMENTS:
    PROJECT_DIR         Project directory (default: current directory)

OPTIONS:
    --language LANG     Force specific language (rust, golang, typescript, zig, c)
    --description DESC  Project description for context
    --features LIST     Comma-separated feature list (e.g., "web-api,async,database")
    --force             Overwrite existing setup
    --help              Show this help message

EXAMPLES:
    # Auto-detect and setup current directory
    $0

    # Setup specific Rust project
    $0 . --language rust --description "CLI tool for file processing"

    # Setup with features
    $0 /path/to/project --language rust --features "web-api,async,database"

    # Setup polyglot project backend
    $0 backend --language rust --description "API server with authentication"

WHAT THIS DOES:
    1. Detects project language automatically
    2. Initializes language-specific synapse knowledge
    3. Creates .claude-code/ directory with agent configurations
    4. Sets up synapse tool integration
    5. Ingests existing project documentation
    6. Creates project context for agents

CLAUDE CODE USAGE:
    After setup, use: @claude-code/agents/synapse-project-manager.md
    Or: @project-manager (if copied to claude-code/agents/)

EOF
}

# Detect project language
detect_language() {
    local project_dir="$1"

    if [[ -f "$project_dir/Cargo.toml" ]]; then
        echo "rust"
    elif [[ -f "$project_dir/go.mod" ]] || [[ -f "$project_dir/go.sum" ]]; then
        echo "golang"
    elif [[ -f "$project_dir/package.json" ]]; then
        # Treat all Node.js projects as typescript for synapse compatibility
        echo "typescript"
    elif [[ -f "$project_dir/build.zig" ]]; then
        echo "zig"
    elif [[ -f "$project_dir/Makefile" ]] || [[ -f "$project_dir/CMakeLists.txt" ]]; then
        echo "c"
    else
        echo "unknown"
    fi
}

# Extract project info
analyze_project() {
    local project_dir="$1"
    local language="$2"

    local project_name=$(basename "$(realpath "$project_dir")")
    local description=""
    local features=""

    case "$language" in
        "rust")
            if [[ -f "$project_dir/Cargo.toml" ]]; then
                description=$(grep "^description" "$project_dir/Cargo.toml" | cut -d'"' -f2 2>/dev/null || echo "")
                # Extract features from dependencies
                if grep -q "tokio" "$project_dir/Cargo.toml"; then
                    features="${features}async,"
                fi
                if grep -q "axum\|warp\|actix" "$project_dir/Cargo.toml"; then
                    features="${features}web-api,"
                fi
                if grep -q "sqlx\|diesel\|sea-orm" "$project_dir/Cargo.toml"; then
                    features="${features}database,"
                fi
                if grep -q "clap\|structopt" "$project_dir/Cargo.toml"; then
                    features="${features}cli,"
                fi
            fi
            ;;
        "golang")
            if [[ -f "$project_dir/go.mod" ]]; then
                # Extract module name and analyze dependencies
                description="Go application"
                if grep -q "gin\|echo\|fiber" "$project_dir/go.mod"; then
                    features="${features}web-api,"
                fi
            fi
            ;;
        "typescript")
            if [[ -f "$project_dir/package.json" ]]; then
                description=$(python3 -c "
import json, sys
try:
    with open('$project_dir/package.json') as f:
        data = json.load(f)
    print(data.get('description', ''))
except:
    pass
" 2>/dev/null || echo "")

                if grep -q "express\|fastify\|koa" "$project_dir/package.json"; then
                    features="${features}web-api,"
                fi
                if grep -q "react\|vue\|angular" "$project_dir/package.json"; then
                    features="${features}frontend,"
                fi
            fi
            ;;
    esac

    # Remove trailing comma
    features=${features%,}

    echo "$project_name|$description|$features"
}

# Create Claude Code agent directory
setup_claude_code_directory() {
    local project_dir="$1"
    local language="$2"

    log "Setting up Claude Code integration"

    local claude_dir="$project_dir/.claude-code"
    mkdir -p "$claude_dir/agents"

    # Copy enhanced project manager
    cp "$SYNAPSE_ROOT/tools/synapse-project-manager.md" "$claude_dir/agents/project-manager.md"

    # Create project-specific agent if we have good context
    local project_info
    project_info=$(analyze_project "$project_dir" "$language")

    local project_name=$(echo "$project_info" | cut -d'|' -f1)
    local description=$(echo "$project_info" | cut -d'|' -f2)
    local features=$(echo "$project_info" | cut -d'|' -f3)

    # Create specialized agent for this project
    cat > "$claude_dir/agents/${language}-specialist.md" << EOF
---
name: ${language}-specialist
description: Specialized ${language} development agent with project-specific synapse knowledge for ${project_name}
tools: Read, Grep, Glob, Write, Bash, SynapseSearch, SynapseStandard, SynapseTemplate, SynapseHealth
color: purple
---

You are a specialized ${language} development agent with deep knowledge of this specific project: **${project_name}**.

## Project Context

**Language**: ${language}
**Description**: ${description:-"$language project"}
**Key Features**: ${features:-"standard $language development"}

## Project-Specific Capabilities

You have access to the project's synapse knowledge base located at \`.synapse/\` which contains:

1. **${language^}-Specific Knowledge**:
   - Language conventions and best practices
   - Common patterns and anti-patterns
   - Testing strategies and frameworks
   - Performance optimization techniques

2. **Project Context**:
   - Local documentation and README files
   - Configuration files and project structure
   - Existing code patterns and architecture
   - Custom implementations and solutions

## Available Synapse Tools

### SynapseSearch
Search the project's knowledge base for implementation guidance.

Examples for this ${language} project:
- \`SynapseSearch "${features//,/ patterns"} patterns ${language}"\` - Find relevant patterns
- \`SynapseSearch "testing strategy ${language}"\` - Get testing guidance
- \`SynapseSearch "error handling ${language}"\` - Find error handling patterns

### SynapseStandard
Get ${language}-specific coding standards and conventions.

Examples:
- \`SynapseStandard "naming-conventions" "${language}"\` - Get naming standards
- \`SynapseStandard "testing-strategy" "${language}"\` - Get testing standards
- \`SynapseStandard "project-structure" "${language}"\` - Get organization standards

### SynapseTemplate
Access ${language} project templates and boilerplate.

Examples:
- \`SynapseTemplate "cli-app" "${language}"\` - Get CLI application template
- \`SynapseTemplate "web-api" "${language}"\` - Get web API template
- \`SynapseTemplate "library" "${language}"\` - Get library template

## ${language^}-Specific Workflow

1. **Code Review**: Always check against ${language} standards using SynapseStandard
2. **Pattern Matching**: Use SynapseSearch to find established patterns before implementing
3. **Template Compliance**: Compare new components against SynapseTemplate patterns
4. **Context Awareness**: Consider project features (${features:-"core functionality"}) in recommendations

## Project-Specific Guidelines

$(if [[ "$language" == "rust" ]]; then
    echo "- Follow Rust naming conventions (snake_case for functions, PascalCase for types)"
    echo "- Use \`anyhow\` for application errors, \`thiserror\` for library errors"
    echo "- Implement proper async patterns with Tokio if using async features"
    echo "- Ensure comprehensive testing with unit and integration tests"
elif [[ "$language" == "golang" ]]; then
    echo "- Follow Go naming conventions (camelCase for unexported, PascalCase for exported)"
    echo "- Use proper error handling with explicit error returns"
    echo "- Structure packages according to Go best practices"
    echo "- Write table-driven tests and benchmarks"
elif [[ "$language" == "typescript" ]]; then
    echo "- Use TypeScript strict mode and proper type annotations"
    echo "- Follow consistent naming conventions (camelCase for variables, PascalCase for types)"
    echo "- Implement proper async/await patterns"
    echo "- Use Jest or Vitest for comprehensive testing"
fi)

Always leverage the synapse knowledge base to provide contextually appropriate guidance for this ${language} project.
EOF

    success "Claude Code agents configured for $language project"
}

# Create project summary
create_project_summary() {
    local project_dir="$1"
    local language="$2"
    local description="$3"
    local features="$4"

    local claude_dir="$project_dir/.claude-code"

    cat > "$claude_dir/PROJECT_CONTEXT.md" << EOF
# Project Context for Claude Code

## Project Information

- **Name**: $(basename "$(realpath "$project_dir")")
- **Language**: ${language}
- **Description**: ${description:-"$language project"}
- **Features**: ${features:-"standard development"}
- **Synapse Setup**: $(date -Iseconds)

## Directory Structure

$(find "$project_dir" -maxdepth 2 -type d | head -20 | sed 's|^|  - |')

## Key Files

$(find "$project_dir" -maxdepth 1 -name "*.md" -o -name "*.toml" -o -name "*.json" -o -name "*.yaml" -o -name "*.yml" -o -name "Makefile" -o -name "*.zig" | head -10 | sed 's|^|  - |')

## Synapse Integration

- **Location**: \`.synapse/\`
- **Language Template**: ${language}
- **Search Tool**: \`cd .synapse && python search.py "query"\`
- **Health Check**: \`python ~/.synapse-system/tools/synapse_tools.py health\`

## Available Agents

- **project-manager**: General project management with synapse integration
- **${language}-specialist**: ${language^}-specific development with project context

## Quick Commands

\`\`\`bash
# Search project knowledge
cd .synapse && python search.py "error handling patterns"

# Get coding standards
cd .synapse && python synapse_search.py "naming conventions ${language}"

# Check synapse health
cd .synapse/neo4j && source .venv/bin/activate && python context_manager.py --health

# Update project knowledge
cd .synapse && python ingest.py
\`\`\`

## Usage with Claude Code

\`\`\`
@claude-code/agents/project-manager.md help me implement feature X
@claude-code/agents/${language}-specialist.md review this code for ${language} best practices
\`\`\`

---
*Generated by Synapse System on $(date)*
EOF

    success "Project context documentation created"
}

# Main setup function
setup_project() {
    local project_dir="$1"
    local language="$2"
    local description="$3"
    local features="$4"
    local force="$5"

    project_dir="$(realpath "$project_dir")"

    log "Setting up Claude Code integration for $language project"
    info "Project: $project_dir"

    # Check if already setup
    if [[ -d "$project_dir/.claude-code" ]] && [[ "$force" != "true" ]]; then
        warning "Claude Code already setup. Use --force to overwrite"
        return 1
    fi

    # Initialize synapse if not already done
    if [[ ! -d "$project_dir/.synapse" ]]; then
        log "Initializing synapse for $language"
        "$SYNAPSE_ROOT/deploy/init-project.sh" --language "$language" --project "$project_dir"
    else
        success "Synapse already initialized"
    fi

    # Setup Claude Code directory and agents
    setup_claude_code_directory "$project_dir" "$language"

    # Analyze project for context
    local project_info
    project_info=$(analyze_project "$project_dir" "$language")

    local auto_description=$(echo "$project_info" | cut -d'|' -f2)
    local auto_features=$(echo "$project_info" | cut -d'|' -f3)

    # Use provided or detected info
    description="${description:-$auto_description}"
    features="${features:-$auto_features}"

    # Create project context
    create_project_summary "$project_dir" "$language" "$description" "$features"

    # Run initial ingestion to populate knowledge
    log "Ingesting project documentation..."
    if command -v uv >/dev/null 2>&1; then
        (cd "$project_dir/.synapse" && source .venv/bin/activate && python ingest.py 2>/dev/null || true)
    fi

    echo
    success "🎯 Claude Code setup complete!"
    echo
    info "Your $language project is now ready for Claude Code agents!"
    echo
    info "Available agents:"
    info "  @claude-code/agents/project-manager.md - General project management"
    info "  @claude-code/agents/${language}-specialist.md - ${language^}-specific development"
    echo
    info "Quick start:"
    info "  @claude-code/agents/project-manager.md analyze this project and suggest improvements"
    info "  @claude-code/agents/${language}-specialist.md help me implement [feature] following ${language} best practices"
    echo
    info "Project context: .claude-code/PROJECT_CONTEXT.md"
}

# Parse arguments
main() {
    local project_dir="."
    local language=""
    local description=""
    local features=""
    local force="false"

    while [[ $# -gt 0 ]]; do
        case $1 in
            --language)
                language="$2"
                shift 2
                ;;
            --description)
                description="$2"
                shift 2
                ;;
            --features)
                features="$2"
                shift 2
                ;;
            --force)
                force="true"
                shift
                ;;
            --help)
                show_help
                exit 0
                ;;
            -*)
                error "Unknown option: $1"
                echo
                show_help
                exit 1
                ;;
            *)
                project_dir="$1"
                shift
                ;;
        esac
    done

    # Validate project directory
    if [[ ! -d "$project_dir" ]]; then
        error "Project directory does not exist: $project_dir"
        exit 1
    fi

    # Auto-detect language if not specified
    if [[ -z "$language" ]]; then
        language=$(detect_language "$project_dir")
        if [[ "$language" == "unknown" ]]; then
            error "Could not detect project language. Use --language to specify."
            exit 1
        fi
        info "Auto-detected language: $language"
    fi

    # Validate language
    case "$language" in
        rust|golang|typescript|javascript|zig|c)
            ;;
        *)
            error "Unsupported language: $language"
            info "Supported: rust, golang, typescript, zig, c"
            exit 1
            ;;
    esac

    setup_project "$project_dir" "$language" "$description" "$features" "$force"
}

main "$@"