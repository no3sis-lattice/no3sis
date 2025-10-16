#!/bin/bash
# CI Script: Build Lean4 proofs
# Extracted from inline workflow script for DRY compliance

set -euo pipefail

# Parse arguments
MODE="${1:-pilots}"  # "pilots" or "all"
PILOTS=(Chunk06 Chunk08 Chunk09 Chunk19)

# Change to formal directory
SCRIPT_DIR="$(dirname "$0")"
cd "$SCRIPT_DIR/../../formal" || exit 1

# Ensure lake-manifest exists
if [ ! -f lake-manifest.json ]; then
    echo "Updating Lake dependencies..."
    lake update
fi

build_pilots() {
    echo "=== Building pilot chunks ==="
    local success=0
    local total="${#PILOTS[@]}"

    for chunk in "${PILOTS[@]}"; do
        echo "Building Duality.Chunks.$chunk..."
        if lake build "Duality.Chunks.$chunk"; then
            success=$((success + 1))
            echo "✓ $chunk built successfully"
        else
            echo "❌ Failed to build $chunk"
        fi
    done

    echo ""
    echo "✓ Lean4 build: $success/$total pilot chunks passed"
    [ $success -eq $total ] || exit 1
}

build_all() {
    echo "=== Building Duality.lean (imports all chunks) ==="
    if lake build Duality; then
        echo "✓ All chunks built successfully"
    else
        echo "❌ Failed to build Duality"
        exit 1
    fi
}

# Main execution
case "$MODE" in
    pilots)
        build_pilots
        ;;
    all)
        build_all
        ;;
    *)
        echo "Usage: $0 [pilots|all]"
        exit 1
        ;;
esac