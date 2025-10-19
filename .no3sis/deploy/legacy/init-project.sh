#!/bin/bash
# Synapse System Project Initializer
# ==================================
#
# Initializes a language-specific Synapse instance in a project directory
# Supports multiple languages and can handle polyglot projects

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
    echo -e "${BLUE}[SYNAPSE-INIT]${NC} $1"
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

# Usage information
show_help() {
    cat << EOF
Synapse System Project Initializer

USAGE:
    $0 --language LANG --project DIR [OPTIONS]

ARGUMENTS:
    --language LANG     Target language (rust, golang, typescript, zig, c)
    --project DIR       Project directory (absolute or relative path)

OPTIONS:
    --subdir SUBDIR     Initialize in subdirectory (for polyglot projects)
    --global-sync       Sync with global synapse knowledge base
    --force             Overwrite existing synapse installation
    --help              Show this help message

EXAMPLES:
    # Initialize Rust synapse in current directory
    $0 --language rust --project .

    # Initialize Go synapse in specific project
    $0 --language golang --project /path/to/go-project

    # Initialize TypeScript synapse in backend subdirectory
    $0 --language typescript --project . --subdir backend

    # Polyglot project: Rust backend + TypeScript frontend
    $0 --language rust --project . --subdir backend
    $0 --language typescript --project . --subdir frontend

SUPPORTED LANGUAGES:
    rust        - Rust projects with Cargo
    golang      - Go projects with modules
    typescript  - TypeScript/JavaScript projects with npm/yarn
    zig         - Zig projects
    c           - C projects with make/cmake

EOF
}

# Detect project language automatically
detect_language() {
    local project_dir="$1"

    if [[ -f "$project_dir/Cargo.toml" ]]; then
        echo "rust"
    elif [[ -f "$project_dir/go.mod" ]] || [[ -f "$project_dir/go.sum" ]]; then
        echo "golang"
    elif [[ -f "$project_dir/package.json" ]]; then
        if grep -q "typescript" "$project_dir/package.json" 2>/dev/null; then
            echo "typescript"
        else
            echo "javascript"
        fi
    elif [[ -f "$project_dir/build.zig" ]]; then
        echo "zig"
    elif [[ -f "$project_dir/Makefile" ]] || [[ -f "$project_dir/CMakeLists.txt" ]]; then
        echo "c"
    else
        echo "unknown"
    fi
}

# Validate language support
validate_language() {
    local language="$1"
    local supported_languages=("rust" "golang" "typescript" "zig" "c")

    for lang in "${supported_languages[@]}"; do
        if [[ "$lang" == "$language" ]]; then
            return 0
        fi
    done

    error "Unsupported language: $language"
    info "Supported languages: ${supported_languages[*]}"
    return 1
}

# Check if directory exists and is writable
validate_project_dir() {
    local project_dir="$1"

    if [[ ! -d "$project_dir" ]]; then
        error "Project directory does not exist: $project_dir"
        return 1
    fi

    if [[ ! -w "$project_dir" ]]; then
        error "Project directory is not writable: $project_dir"
        return 1
    fi

    return 0
}

# Check if synapse is already installed
check_existing_installation() {
    local target_dir="$1"
    local force="$2"

    if [[ -d "$target_dir/.synapse" ]]; then
        if [[ "$force" == "true" ]]; then
            warning "Overwriting existing synapse installation in $target_dir"
            rm -rf "$target_dir/.synapse"
        else
            error "Synapse already installed in $target_dir"
            info "Use --force to overwrite existing installation"
            return 1
        fi
    fi

    return 0
}

# Copy language-specific templates
copy_language_template() {
    local language="$1"
    local target_dir="$2"

    local template_dir="$SYNAPSE_ROOT/languages/$language"

    if [[ ! -d "$template_dir" ]]; then
        error "Language template not found: $template_dir"
        return 1
    fi

    log "Copying $language template to $target_dir/.synapse"

    # Create synapse directory structure
    mkdir -p "$target_dir/.synapse"/{instructions,standards,templates,tools}

    # Copy language-specific content
    if [[ -d "$template_dir/instructions" ]]; then
        cp -r "$template_dir/instructions"/* "$target_dir/.synapse/instructions/" 2>/dev/null || true
    fi

    if [[ -d "$template_dir/standards" ]]; then
        cp -r "$template_dir/standards"/* "$target_dir/.synapse/standards/" 2>/dev/null || true
    fi

    if [[ -d "$template_dir/templates" ]]; then
        cp -r "$template_dir/templates"/* "$target_dir/.synapse/templates/" 2>/dev/null || true
    fi

    success "Language template copied"
}

# Copy core synapse engine
copy_synapse_core() {
    local target_dir="$1"

    log "Copying synapse core engine"

    # Copy core Python modules
    cp "$SYNAPSE_ROOT/neo4j/context_manager.py" "$target_dir/.synapse/"
    cp "$SYNAPSE_ROOT/neo4j/vector_engine.py" "$target_dir/.synapse/"
    cp "$SYNAPSE_ROOT/neo4j/requirements-minimal.txt" "$target_dir/.synapse/"

    # Copy and customize configuration
    cp "$SYNAPSE_ROOT/neo4j/.env.example" "$target_dir/.synapse/"

    success "Core engine copied"
}

# Create project-specific configuration
create_project_config() {
    local target_dir="$1"
    local language="$2"
    local project_name="$(basename "$(realpath "$target_dir")")"

    log "Creating project configuration"

    cat > "$target_dir/.synapse/config.json" << EOF
{
    "project_name": "$project_name",
    "language": "$language",
    "synapse_version": "2.0.0",
    "created_at": "$(date -Iseconds)",
    "global_sync_enabled": false,
    "vector_model": "simple_tfidf",
    "cache_ttl": 3600
}
EOF

    success "Project configuration created"
}

# Create project setup script
create_setup_script() {
    local target_dir="$1"
    local language="$2"

    log "Creating project setup script"

    cat > "$target_dir/.synapse/setup.sh" << 'EOF'
#!/bin/bash
# Project-specific Synapse Setup
set -e

SYNAPSE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SYNAPSE_DIR")"

echo "Setting up Synapse for project: $(basename "$PROJECT_ROOT")"

# Create Python virtual environment
if [ ! -d "$SYNAPSE_DIR/.venv" ]; then
    echo "Creating Python virtual environment..."
    cd "$SYNAPSE_DIR"
    uv venv
    source .venv/bin/activate
    uv pip install -r requirements-minimal.txt
    echo "✓ Python environment ready"
fi

# Initialize vector store
echo "Initializing vector storage..."
cd "$SYNAPSE_DIR"
source .venv/bin/activate
python -c "
from vector_engine import VectorEngine
engine = VectorEngine()
engine.initialize_vector_store()
print('✓ Vector storage initialized')
"

# Create project-specific synapse search tool
cat > "$SYNAPSE_DIR/search.py" << 'SEARCH_EOF'
#!/usr/bin/env python3
"""Project-specific Synapse Search Tool"""

import sys
import os
import json
from pathlib import Path

# Add current directory to path
sys.path.insert(0, os.path.dirname(__file__))

from context_manager import SynapseContextManager
from vector_engine import VectorEngine

def search_project_context(query: str, max_results: int = 5):
    """Search project-specific synapse context"""
    synapse_dir = Path(__file__).parent

    # Override synapse root to point to project
    manager = SynapseContextManager()
    manager.synapse_root = synapse_dir.parent
    manager.sqlite_path = synapse_dir / "vector_store.db"
    manager.vector_engine = VectorEngine(synapse_dir.parent)

    try:
        return manager.intelligent_search(query, max_results)
    finally:
        manager.close()

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python search.py <query>")
        sys.exit(1)

    query = " ".join(sys.argv[1:])
    result = search_project_context(query)
    print(json.dumps(result, indent=2))
SEARCH_EOF

chmod +x "$SYNAPSE_DIR/search.py"

echo "✓ Synapse setup complete!"
echo
echo "Next steps:"
echo "  1. Run ingestion: cd .synapse && python ingest.py"
echo "  2. Test search: cd .synapse && python search.py 'your query'"
EOF

    chmod +x "$target_dir/.synapse/setup.sh"
    success "Setup script created"
}

# Create project ingestion script
create_ingestion_script() {
    local target_dir="$1"

    log "Creating project ingestion script"

    cat > "$target_dir/.synapse/ingest.py" << 'EOF'
#!/usr/bin/env python3
"""Project-specific Synapse Ingestion"""

import sys
import os
from pathlib import Path

# Add current directory to path
sys.path.insert(0, os.path.dirname(__file__))

# Import the enhanced ingestion system
sys.path.insert(0, os.path.expanduser("~/.synapse-system/.synapse/neo4j"))
from ingestion import SynapseIngestion

class ProjectSynapseIngestion(SynapseIngestion):
    """Project-specific ingestion that processes project files"""

    def __init__(self):
        super().__init__()
        # Override synapse root to point to project directory
        self.synapse_root = Path(__file__).parent.parent
        self.sqlite_path = Path(__file__).parent / "vector_store.db"

    def discover_files(self):
        """Discover files in project directory"""
        files = []
        project_root = self.synapse_root

        # Include synapse-specific files
        synapse_dir = project_root / ".synapse"
        for pattern in ["*.md", "*.py", "*.txt"]:
            files.extend(synapse_dir.rglob(pattern))

        # Include project documentation
        for pattern in ["*.md", "*.rst", "*.txt"]:
            files.extend(project_root.glob(pattern))
            files.extend(project_root.glob(f"docs/**/{pattern}"))

        # Include project configuration files
        config_files = [
            "Cargo.toml", "package.json", "go.mod", "pyproject.toml",
            "Makefile", "CMakeLists.txt", "build.zig"
        ]

        for config_file in config_files:
            config_path = project_root / config_file
            if config_path.exists():
                files.append(config_path)

        print(f"✓ Discovered {len(files)} files for processing")
        return files

if __name__ == "__main__":
    import sys

    force_refresh = "--force" in sys.argv

    if "--help" in sys.argv:
        print("Project Synapse Ingestion")
        print()
        print("Usage: python ingest.py [--force]")
        print()
        print("Options:")
        print("  --force    Force full refresh")
        print("  --help     Show this help")
        sys.exit(0)

    ingestion = ProjectSynapseIngestion()
    try:
        success = ingestion.run_full_ingestion(force_refresh=force_refresh)
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print("\n⚠️  Ingestion interrupted")
        sys.exit(1)
    except Exception as e:
        print(f"✗ Error: {e}")
        sys.exit(1)
    finally:
        ingestion.close()
EOF

    chmod +x "$target_dir/.synapse/ingest.py"
    success "Ingestion script created"
}

# Main initialization function
initialize_project() {
    local language="$1"
    local project_dir="$2"
    local subdir="$3"
    local force="$4"
    local global_sync="$5"

    # Determine target directory
    local target_dir="$project_dir"
    if [[ -n "$subdir" ]]; then
        target_dir="$project_dir/$subdir"
        mkdir -p "$target_dir"
    fi

    target_dir="$(realpath "$target_dir")"

    log "Initializing Synapse for $language project in $target_dir"

    # Validation
    validate_language "$language" || return 1
    validate_project_dir "$target_dir" || return 1
    check_existing_installation "$target_dir" "$force" || return 1

    # Copy templates and core
    copy_language_template "$language" "$target_dir" || return 1
    copy_synapse_core "$target_dir" || return 1

    # Create project-specific files
    create_project_config "$target_dir" "$language" || return 1
    create_setup_script "$target_dir" "$language" || return 1
    create_ingestion_script "$target_dir" || return 1

    # Run setup
    log "Running initial setup..."
    (cd "$target_dir/.synapse" && ./setup.sh)

    success "Project synapse initialization complete!"
    echo
    info "Synapse installed in: $target_dir/.synapse"
    info "Language: $language"
    echo
    info "Next steps:"
    info "  1. cd $target_dir/.synapse"
    info "  2. python ingest.py  # Process project files"
    info "  3. python search.py 'your query'  # Test search"
}

# Parse command line arguments
main() {
    local language=""
    local project_dir=""
    local subdir=""
    local force="false"
    local global_sync="false"

    while [[ $# -gt 0 ]]; do
        case $1 in
            --language)
                language="$2"
                shift 2
                ;;
            --project)
                project_dir="$2"
                shift 2
                ;;
            --subdir)
                subdir="$2"
                shift 2
                ;;
            --force)
                force="true"
                shift
                ;;
            --global-sync)
                global_sync="true"
                shift
                ;;
            --help)
                show_help
                exit 0
                ;;
            *)
                error "Unknown option: $1"
                echo
                show_help
                exit 1
                ;;
        esac
    done

    # Check required arguments
    if [[ -z "$language" ]]; then
        error "Language is required"
        echo
        show_help
        exit 1
    fi

    if [[ -z "$project_dir" ]]; then
        error "Project directory is required"
        echo
        show_help
        exit 1
    fi

    # Auto-detect language if not specified or validate
    if [[ "$language" == "auto" ]]; then
        target_dir="$project_dir"
        if [[ -n "$subdir" ]]; then
            target_dir="$project_dir/$subdir"
        fi

        detected_language=$(detect_language "$target_dir")
        if [[ "$detected_language" == "unknown" ]]; then
            error "Could not auto-detect language in $target_dir"
            exit 1
        fi

        language="$detected_language"
        info "Auto-detected language: $language"
    fi

    # Initialize the project
    initialize_project "$language" "$project_dir" "$subdir" "$force" "$global_sync"
}

# Run main function
main "$@"