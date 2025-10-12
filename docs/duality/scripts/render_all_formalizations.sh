#!/usr/bin/env bash
# Render all 62 MiniZinc and Lean4 files from constraints
set -euo pipefail

cd "$(dirname "$0")/.."
CHUNKS_DIR="true-dual-tract/chunks"

rendered_mzn=0
rendered_lean=0
skipped=0
errors=0

echo "Rendering formalizations for 62 chunks..."

for i in $(seq -w 1 62); do
    json_file="${CHUNKS_DIR}/chunk-${i}.constraints.json"
    mzn_file="${CHUNKS_DIR}/chunk-${i}.mzn"
    lean_file="${CHUNKS_DIR}/chunk-${i}.lean"

    if [[ ! -f "$json_file" ]]; then
        echo "ERROR: Missing $json_file"
        ((errors++))
        continue
    fi

    # Skip if already rendered
    if [[ -f "$mzn_file" && -f "$lean_file" ]]; then
        ((skipped++))
        continue
    fi

    # Render
    if python3 scripts/render_formalizations.py "$json_file" 2>&1 | grep -q "Rendered"; then
        ((rendered_mzn++))
        ((rendered_lean++))
    else
        echo "ERROR: Failed to render chunk-${i}"
        ((errors++))
    fi
done

echo ""
echo "Summary:"
echo "  MiniZinc files rendered: $rendered_mzn"
echo "  Lean4 files rendered: $rendered_lean"
echo "  Skipped (already exist): $skipped"
echo "  Errors: $errors"

if [[ $errors -gt 0 ]]; then
    exit 1
fi
