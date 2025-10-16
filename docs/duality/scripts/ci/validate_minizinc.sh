#!/bin/bash
# CI Script: Validate MiniZinc models
# Extracted from inline workflow script for DRY compliance

set -euo pipefail

# Parse arguments
MODE="${1:-all}"  # "pilots" or "all"
PILOTS=(06 08 09 19)

# Change to chunks directory
cd "$(dirname "$0")/../../true-dual-tract/chunks" || exit 1

validate_pilots() {
    local success=0
    local total=0

    for chunk in "${PILOTS[@]}"; do
        total=$((total + 1))
        echo "=== Validating Chunk $chunk MiniZinc ==="
        if minizinc -e "chunk-${chunk}.mzn" 2>&1; then
            success=$((success + 1))
            echo "✓ chunk-${chunk}.mzn passed"
        else
            echo "❌ Failed: chunk-${chunk}.mzn"
        fi
    done

    echo ""
    echo "✓ MiniZinc validation: $success/$total pilot files passed"
    [ $success -eq $total ] || exit 1
}

validate_all() {
    local success=0
    local total=0
    local failed_chunks=""

    for f in chunk-*.mzn; do
        [ -f "$f" ] || continue  # Handle no matches
        total=$((total + 1))
        chunk_id=$(echo "$f" | sed 's/chunk-\([0-9]*\)\.mzn/\1/')

        echo "=== Validating $f ==="
        if minizinc -e "$f" 2>&1; then
            success=$((success + 1))
        else
            echo "❌ Failed: $f"
            failed_chunks="$failed_chunks $chunk_id"
        fi
    done

    echo ""
    echo "✓ MiniZinc validation: $success/$total files passed"

    if [ $success -ne $total ]; then
        echo "Failed chunks:$failed_chunks"
        exit 1
    fi
}

# Main execution
case "$MODE" in
    pilots)
        validate_pilots
        ;;
    all)
        validate_all
        ;;
    *)
        echo "Usage: $0 [pilots|all]"
        exit 1
        ;;
esac