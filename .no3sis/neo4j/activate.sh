#!/bin/bash
# Synapse System Activation Script
# ================================
#
# The master script for health checks, service startup, and automatic ingestion.
# This implements the OODA Loop: Observe -> Orient -> Decide -> Act
#
# Zone-0 Axiom: The system must be self-healing and self-updating.

set -e  # Exit on any error

# Configuration - Detect if we're in project or global mode
if [[ -f "./neo4j/activate.sh" && -d "./instructions" ]]; then
    # We're in a project's .synapse directory
    SYNAPSE_ROOT="$(pwd)"
    NEO4J_DIR="$SYNAPSE_ROOT/neo4j"
elif [[ -d "$HOME/.synapse-system/.synapse" ]]; then
    # Global synapse system
    SYNAPSE_ROOT="$HOME/.synapse-system/.synapse"
    NEO4J_DIR="$SYNAPSE_ROOT/neo4j"
else
    # Fallback to old structure
    SYNAPSE_ROOT="$HOME/.synapse-system"
    NEO4J_DIR="$SYNAPSE_ROOT/neo4j"
fi
VENV_DIR="$NEO4J_DIR/.venv"
COMPOSE_FILE="$NEO4J_DIR/docker-compose.yml"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Logging function
log() {
    echo -e "${BLUE}[SYNAPSE]${NC} $1"
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

# Check if we're in the correct directory structure
check_environment() {
    log "Checking environment setup..."

    if [ ! -d "$SYNAPSE_ROOT" ]; then
        error "Synapse root directory not found: $SYNAPSE_ROOT"
        exit 1
    fi

    if [ ! -d "$NEO4J_DIR" ]; then
        error "Neo4j directory not found: $NEO4J_DIR"
        exit 1
    fi

    if [ ! -f "$COMPOSE_FILE" ]; then
        error "Docker compose file not found: $COMPOSE_FILE"
        exit 1
    fi

    success "Environment structure verified"
}

# Check if Docker is available and running
check_docker() {
    log "Checking Docker availability..."

    if ! command -v docker &> /dev/null; then
        error "Docker is not installed or not in PATH"
        exit 1
    fi

    if ! docker info &> /dev/null; then
        error "Docker daemon is not running"
        exit 1
    fi

    if ! command -v docker-compose &> /dev/null && ! docker compose version &> /dev/null; then
        error "Docker Compose is not available"
        exit 1
    fi

    success "Docker is available and running"
}

# Start services using Docker Compose
start_services() {
    log "Starting Neo4j and Redis services..."

    cd "$NEO4J_DIR"

    # Use docker-compose or docker compose based on availability
    if command -v docker-compose &> /dev/null; then
        COMPOSE_CMD="docker-compose"
    else
        COMPOSE_CMD="docker compose"
    fi

    # Start services in detached mode
    $COMPOSE_CMD up -d

    # Wait for services to be ready
    log "Waiting for services to be ready..."
    sleep 10

    # Check Neo4j health
    local neo4j_ready=false
    for i in {1..30}; do
        if curl -s http://localhost:7474 > /dev/null 2>&1; then
            neo4j_ready=true
            break
        fi
        sleep 2
    done

    if [ "$neo4j_ready" = true ]; then
        success "Neo4j is ready"
    else
        warning "Neo4j may not be fully ready yet"
    fi

    # Check Redis health
    if docker exec "${NEO4J_DIR##*/}_redis_1" redis-cli ping > /dev/null 2>&1 || \
       docker exec "${NEO4J_DIR##*/}-redis-1" redis-cli ping > /dev/null 2>&1; then
        success "Redis is ready"
    else
        warning "Redis may not be fully ready yet"
    fi

    success "Services started successfully"
}

# Check service health using Python scripts
check_service_health() {
    log "Checking service health using context manager..."

    cd "$NEO4J_DIR"

    # Activate virtual environment
    if [ -f "$VENV_DIR/bin/activate" ]; then
        source "$VENV_DIR/bin/activate"
    else
        error "Python virtual environment not found"
        return 1
    fi

    # Check health using our Python script
    local health_output
    health_output=$(python context_manager.py --health 2>&1)
    local health_exit_code=$?

    if [ $health_exit_code -eq 0 ]; then
        success "Service health check passed"
        # Parse health status for detailed reporting
        if echo "$health_output" | grep -q '"status": "healthy"'; then
            success "All services are healthy"
            return 0
        else
            warning "Some services may have issues"
            echo "$health_output"
            return 1
        fi
    else
        error "Health check failed"
        echo "$health_output"
        return 1
    fi
}

# Check if data is stale and needs re-ingestion
check_staleness() {
    log "Checking data staleness..."

    cd "$NEO4J_DIR"

    # Activate virtual environment
    source "$VENV_DIR/bin/activate"

    if python context_manager.py --stale 2>&1 | grep -q "stale"; then
        warning "Data is stale and needs re-ingestion"
        return 1
    else
        success "Data is fresh"
        return 0
    fi
}

# Run the ingestion process
run_ingestion() {
    log "Running ingestion process..."

    cd "$NEO4J_DIR"

    # Activate virtual environment
    source "$VENV_DIR/bin/activate"

    # Run ingestion
    if python ingestion.py; then
        success "Ingestion completed successfully"
        return 0
    else
        error "Ingestion failed"
        return 1
    fi
}

# Create sample files if synapse system is empty
create_sample_files() {
    log "Creating sample synapse files for demonstration..."

    # Create a sample instruction file
    mkdir -p "$SYNAPSE_ROOT/instructions"

    if [ ! -f "$SYNAPSE_ROOT/instructions/sample-instruction.md" ]; then
        cat > "$SYNAPSE_ROOT/instructions/sample-instruction.md" << 'EOF'
# Sample Instruction: Execute Task

This is a sample instruction file demonstrating the synapse system.

## Purpose
This instruction guides agents through task execution with proper error handling.

## Implementation
1. Parse the task requirements
2. Break down into manageable steps
3. Execute with error checking
4. Report results

## Commands
- `execute-task --input <task>`: Main execution command
- `validate-task --task <task>`: Validation command
EOF
        success "Created sample instruction file"
    fi

    # Create a sample standard file
    mkdir -p "$SYNAPSE_ROOT/standards"

    if [ ! -f "$SYNAPSE_ROOT/standards/coding-standards.md" ]; then
        cat > "$SYNAPSE_ROOT/standards/coding-standards.md" << 'EOF'
# Coding Standards

Following the Numogrammatic Codex principles:

## Core Axioms
- KISS: Keep implementations simple
- DRY: Single source of truth
- SoC: Separate concerns cleanly

## Quality Gates
- All code must pass tests
- Functions should have single responsibility
- Interfaces should be segregated

## Error Handling
Follow the Five Whys methodology for root cause analysis.
EOF
        success "Created sample standards file"
    fi
}

# Display status summary
show_status() {
    log "=== SYNAPSE SYSTEM STATUS ==="

    cd "$NEO4J_DIR"
    source "$VENV_DIR/bin/activate"

    echo
    log "Health Status:"
    python context_manager.py --health | python -m json.tool

    echo
    log "Data Freshness:"
    if python context_manager.py --stale 2>&1 | grep -q "fresh"; then
        success "Data is up to date"
    else
        warning "Data may be stale"
    fi

    echo
    log "Services:"
    cd "$NEO4J_DIR"
    if command -v docker-compose &> /dev/null; then
        docker-compose ps
    else
        docker compose ps
    fi
}

# Main execution flow - The OODA Loop implementation
main() {
    echo
    log "🧠 Synapse System Activation Initiated"
    log "Implementing OODA Loop: Observe -> Orient -> Decide -> Act"
    echo

    # OBSERVE: Check current state
    log "OBSERVE: Checking current system state..."
    check_environment
    check_docker

    # ORIENT: Understand what needs to be done
    log "ORIENT: Analyzing service requirements..."

    # Start services (always ensure they're running)
    start_services

    # DECIDE: Determine if re-ingestion is needed
    log "DECIDE: Evaluating data freshness..."

    local needs_ingestion=false

    # Check if services are healthy
    if ! check_service_health; then
        warning "Service health issues detected"
        needs_ingestion=true
    fi

    # Check if data is stale
    if ! check_staleness; then
        needs_ingestion=true
    fi

    # Check if we have any data at all
    cd "$NEO4J_DIR"
    source "$VENV_DIR/bin/activate"
    local file_count
    file_count=$(python context_manager.py --health 2>/dev/null | grep -o '"count": [0-9]*' | grep -o '[0-9]*' || echo "0")

    if [ "$file_count" -eq 0 ]; then
        log "No files found in system, creating samples and ingesting..."
        create_sample_files
        needs_ingestion=true
    fi

    # ACT: Perform ingestion if needed
    if [ "$needs_ingestion" = true ]; then
        log "ACT: Running data ingestion..."
        if ! run_ingestion; then
            error "Failed to complete ingestion"
            exit 1
        fi
    else
        success "No ingestion needed - system is up to date"
    fi

    # Final status check
    echo
    log "VERIFICATION: Final system check..."
    if check_service_health; then
        success "🎯 Synapse System is fully operational"
        show_status
    else
        error "❌ System activation completed with issues"
        exit 1
    fi

    echo
    success "✅ Activation complete. You can now use the synapse system for intelligent context retrieval."
    echo
}

# Handle script arguments
case "${1:-}" in
    "--help"|"-h")
        echo "Synapse System Activation Script"
        echo
        echo "Usage: $0 [OPTIONS]"
        echo
        echo "Options:"
        echo "  --help, -h     Show this help message"
        echo "  --status, -s   Show current system status"
        echo "  --force, -f    Force re-ingestion even if data is fresh"
        echo "  --stop         Stop all services"
        echo
        echo "Default: Run full activation workflow"
        exit 0
        ;;
    "--status"|"-s")
        check_environment
        show_status
        exit 0
        ;;
    "--force"|"-f")
        log "Force mode: Will re-ingest data regardless of freshness"
        check_environment
        check_docker
        start_services
        sleep 5
        create_sample_files
        run_ingestion
        show_status
        exit 0
        ;;
    "--stop")
        log "Stopping Synapse services..."
        cd "$NEO4J_DIR"
        if command -v docker-compose &> /dev/null; then
            docker-compose down
        else
            docker compose down
        fi
        success "Services stopped"
        exit 0
        ;;
    "")
        # Default: run main workflow
        main
        ;;
    *)
        error "Unknown option: $1"
        echo "Use --help for usage information"
        exit 1
        ;;
esac