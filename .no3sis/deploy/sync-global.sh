#!/bin/bash
# Synapse Global Sync Script
# ==========================
#
# Syncs knowledge between global synapse and project-local instances

set -e

# Configuration
SYNAPSE_ROOT="$HOME/.synapse-system"
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
    echo -e "${BLUE}[SYNAPSE-SYNC]${NC} $1"
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
Synapse Global Sync Script

USAGE:
    $0 [COMMAND] [OPTIONS]

COMMANDS:
    pull        Pull global knowledge to project
    push        Push project knowledge to global (with filtering)
    status      Show sync status
    help        Show this help message

OPTIONS:
    --project DIR    Project directory (default: current directory)
    --force          Force overwrite conflicts
    --dry-run        Show what would be synced without making changes

EXAMPLES:
    # Pull global updates to current project
    $0 pull

    # Push valuable project patterns to global
    $0 push --dry-run

    # Check sync status
    $0 status --project /path/to/project

EOF
}

find_project_synapse() {
    local project_dir="${1:-.}"
    local synapse_path="$project_dir/.synapse"

    if [[ -d "$synapse_path" ]] && [[ -f "$synapse_path/config.json" ]]; then
        echo "$synapse_path"
        return 0
    fi

    error "No synapse installation found in $project_dir"
    return 1
}

get_project_config() {
    local synapse_path="$1"
    local config_file="$synapse_path/config.json"

    if [[ -f "$config_file" ]]; then
        cat "$config_file"
    else
        echo "{}"
    fi
}

pull_global_knowledge() {
    local project_dir="$1"
    local force="$2"

    log "Pulling global knowledge to project"

    local synapse_path
    synapse_path=$(find_project_synapse "$project_dir") || return 1

    local config
    config=$(get_project_config "$synapse_path")

    local language
    language=$(echo "$config" | python3 -c "import sys, json; data=json.load(sys.stdin); print(data.get('language', 'unknown'))")

    if [[ "$language" == "unknown" ]]; then
        warning "Unknown project language, pulling generic knowledge"
        language=""
    else
        info "Project language: $language"
    fi

    # Pull generic knowledge
    log "Pulling generic standards and instructions..."

    if [[ -d "$SYNAPSE_ROOT/instructions" ]]; then
        cp -r "$SYNAPSE_ROOT/instructions"/* "$synapse_path/instructions/" 2>/dev/null || true
    fi

    if [[ -d "$SYNAPSE_ROOT/standards" ]]; then
        cp -r "$SYNAPSE_ROOT/standards"/* "$synapse_path/standards/" 2>/dev/null || true
    fi

    # Pull language-specific knowledge if available
    if [[ -n "$language" ]] && [[ -d "$SYNAPSE_ROOT/languages/$language" ]]; then
        log "Pulling $language-specific knowledge..."

        if [[ -d "$SYNAPSE_ROOT/languages/$language/instructions" ]]; then
            cp -r "$SYNAPSE_ROOT/languages/$language/instructions"/* "$synapse_path/instructions/" 2>/dev/null || true
        fi

        if [[ -d "$SYNAPSE_ROOT/languages/$language/standards" ]]; then
            cp -r "$SYNAPSE_ROOT/languages/$language/standards"/* "$synapse_path/standards/" 2>/dev/null || true
        fi

        if [[ -d "$SYNAPSE_ROOT/languages/$language/templates" ]]; then
            mkdir -p "$synapse_path/templates"
            cp -r "$SYNAPSE_ROOT/languages/$language/templates"/* "$synapse_path/templates/" 2>/dev/null || true
        fi
    fi

    # Update sync metadata
    local sync_metadata="{
        \"last_pull\": \"$(date -Iseconds)\",
        \"global_version\": \"2.0.0\",
        \"language\": \"$language\"
    }"

    echo "$sync_metadata" > "$synapse_path/sync_metadata.json"

    success "Global knowledge pulled successfully"
}

push_project_knowledge() {
    local project_dir="$1"
    local dry_run="$2"

    log "Analyzing project knowledge for global contribution"

    local synapse_path
    synapse_path=$(find_project_synapse "$project_dir") || return 1

    local config
    config=$(get_project_config "$synapse_path")

    local language
    language=$(echo "$config" | python3 -c "import sys, json; data=json.load(sys.stdin); print(data.get('language', 'unknown'))")

    if [[ "$language" == "unknown" ]]; then
        warning "Cannot determine project language for push"
        return 1
    fi

    info "Analyzing $language project for valuable patterns..."

    # Look for custom instructions, standards, or templates
    local contributions=()

    # Check for custom instructions
    if [[ -d "$synapse_path/instructions" ]]; then
        while IFS= read -r -d '' file; do
            local basename=$(basename "$file")
            local global_equivalent="$SYNAPSE_ROOT/languages/$language/instructions/$basename"

            if [[ ! -f "$global_equivalent" ]]; then
                contributions+=("instruction:$file")
            fi
        done < <(find "$synapse_path/instructions" -name "*.md" -print0)
    fi

    # Check for custom standards
    if [[ -d "$synapse_path/standards" ]]; then
        while IFS= read -r -d '' file; do
            local basename=$(basename "$file")
            local global_equivalent="$SYNAPSE_ROOT/languages/$language/standards/$basename"

            if [[ ! -f "$global_equivalent" ]]; then
                contributions+=("standard:$file")
            fi
        done < <(find "$synapse_path/standards" -name "*.md" -print0)
    fi

    if [[ ${#contributions[@]} -eq 0 ]]; then
        info "No new contributions found to push to global"
        return 0
    fi

    log "Found ${#contributions[@]} potential contributions:"

    for contribution in "${contributions[@]}"; do
        local type="${contribution%%:*}"
        local file="${contribution#*:}"
        local basename=$(basename "$file")

        info "  $type: $basename"

        if [[ "$dry_run" != "true" ]]; then
            local target_dir="$SYNAPSE_ROOT/languages/$language/${type}s"
            mkdir -p "$target_dir"
            cp "$file" "$target_dir/"
            success "Contributed $basename to global $language ${type}s"
        fi
    done

    if [[ "$dry_run" == "true" ]]; then
        info "Dry run complete - no files were actually copied"
    else
        success "Project knowledge pushed to global repository"
    fi
}

show_sync_status() {
    local project_dir="$1"

    log "Checking sync status"

    local synapse_path
    synapse_path=$(find_project_synapse "$project_dir") || return 1

    local config
    config=$(get_project_config "$synapse_path")

    local language
    language=$(echo "$config" | python3 -c "import sys, json; data=json.load(sys.stdin); print(data.get('language', 'unknown'))")

    echo
    info "Project Information:"
    echo "  Path: $synapse_path"
    echo "  Language: $language"

    # Check sync metadata
    local sync_file="$synapse_path/sync_metadata.json"
    if [[ -f "$sync_file" ]]; then
        local last_pull
        last_pull=$(python3 -c "import sys, json; data=json.load(open('$sync_file')); print(data.get('last_pull', 'Never'))")
        echo "  Last Global Pull: $last_pull"
    else
        echo "  Last Global Pull: Never"
    fi

    echo
    info "Global Language Template Status:"
    if [[ -d "$SYNAPSE_ROOT/languages/$language" ]]; then
        echo "  Template Available: Yes"
        echo "  Instructions: $(find "$SYNAPSE_ROOT/languages/$language/instructions" -name "*.md" | wc -l) files"
        echo "  Standards: $(find "$SYNAPSE_ROOT/languages/$language/standards" -name "*.md" | wc -l) files"
        echo "  Templates: $(find "$SYNAPSE_ROOT/languages/$language/templates" -type f | wc -l) files"
    else
        echo "  Template Available: No"
    fi

    echo
    info "Local Synapse Content:"
    echo "  Instructions: $(find "$synapse_path/instructions" -name "*.md" 2>/dev/null | wc -l) files"
    echo "  Standards: $(find "$synapse_path/standards" -name "*.md" 2>/dev/null | wc -l) files"
    echo "  Templates: $(find "$synapse_path/templates" -type f 2>/dev/null | wc -l) files"
}

main() {
    local command=""
    local project_dir="."
    local force="false"
    local dry_run="false"

    while [[ $# -gt 0 ]]; do
        case $1 in
            pull|push|status|help)
                command="$1"
                shift
                ;;
            --project)
                project_dir="$2"
                shift 2
                ;;
            --force)
                force="true"
                shift
                ;;
            --dry-run)
                dry_run="true"
                shift
                ;;
            *)
                error "Unknown option: $1"
                echo
                show_help
                exit 1
                ;;
        esac
    done

    if [[ -z "$command" ]]; then
        error "Command is required"
        echo
        show_help
        exit 1
    fi

    case "$command" in
        pull)
            pull_global_knowledge "$project_dir" "$force"
            ;;
        push)
            push_project_knowledge "$project_dir" "$dry_run"
            ;;
        status)
            show_sync_status "$project_dir"
            ;;
        help)
            show_help
            ;;
    esac
}

main "$@"