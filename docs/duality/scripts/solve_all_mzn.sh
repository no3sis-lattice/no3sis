#!/usr/bin/env bash
# Solve all 62 MiniZinc models in parallel with 60s timeout
set -euo pipefail

cd "$(dirname "$0")/.."
CHUNKS_DIR="true-dual-tract/chunks"
RESULTS_DIR="${CHUNKS_DIR}"
TIMEOUT=60000  # 60 seconds in milliseconds
JOBS=4  # Parallel jobs

echo "Solving 62 chunks with MiniZinc (timeout: ${TIMEOUT}ms, parallel: ${JOBS})"
echo ""

# Function to solve a single chunk
solve_chunk() {
    local i=$1
    local chunk_file="${CHUNKS_DIR}/chunk-${i}.mzn"
    local result_file="${RESULTS_DIR}/chunk-${i}.mzn.result.json"

    if [[ ! -f "$chunk_file" ]]; then
        echo "{\"id\": \"${i}\", \"status\": \"ERROR\", \"message\": \"File not found\"}" > "$result_file"
        echo "✗ chunk-${i} (file not found)"
        return 1
    fi

    local start_time=$(date +%s%3N)
    local output
    local exit_code=0

    # Run minizinc with timeout
    output=$(minizinc --solver Gecode --time-limit "$TIMEOUT" "$chunk_file" 2>&1) || exit_code=$?

    local end_time=$(date +%s%3N)
    local elapsed=$((end_time - start_time))

    # Determine status
    local status
    local solution=""
    if [[ $exit_code -eq 0 ]]; then
        if echo "$output" | grep -q "=====UNSATISFIABLE====="; then
            status="UNSAT"
        elif echo "$output" | grep -q "=====UNBOUNDED====="; then
            status="UNBOUNDED"
        elif echo "$output" | grep -q "x = "; then
            status="SAT"
            solution=$(echo "$output" | grep "x = " | head -1)
        else
            status="UNKNOWN"
        fi
    else
        if echo "$output" | grep -qi "timeout\|time limit"; then
            status="TIMEOUT"
        else
            status="ERROR"
        fi
    fi

    # Write result JSON
    cat > "$result_file" <<EOF
{
  "id": "${i}",
  "status": "$status",
  "time_ms": $elapsed,
  "solution": $([ -n "$solution" ] && echo "\"$solution\"" || echo "null")
}
EOF

    # Print status
    case $status in
        SAT) echo "✓ chunk-${i} ($status, ${elapsed}ms)" ;;
        UNSAT) echo "○ chunk-${i} ($status, ${elapsed}ms)" ;;
        TIMEOUT) echo "⏱ chunk-${i} ($status, ${elapsed}ms)" ;;
        *) echo "✗ chunk-${i} ($status, ${elapsed}ms)" ;;
    esac
}

export -f solve_chunk
export CHUNKS_DIR RESULTS_DIR TIMEOUT

# Solve chunks in parallel
seq -w 1 62 | xargs -P "$JOBS" -I {} bash -c 'solve_chunk {}'

echo ""
echo "Analyzing results..."

# Count results
sat=$(grep -l '"status": "SAT"' "${RESULTS_DIR}"/chunk-*.mzn.result.json 2>/dev/null | wc -l)
unsat=$(grep -l '"status": "UNSAT"' "${RESULTS_DIR}"/chunk-*.mzn.result.json 2>/dev/null | wc -l)
timeout=$(grep -l '"status": "TIMEOUT"' "${RESULTS_DIR}"/chunk-*.mzn.result.json 2>/dev/null | wc -l)
error=$(grep -l '"status": "ERROR"' "${RESULTS_DIR}"/chunk-*.mzn.result.json 2>/dev/null | wc -l)
unknown=$(grep -l '"status": "UNKNOWN"' "${RESULTS_DIR}"/chunk-*.mzn.result.json 2>/dev/null | wc -l)

echo ""
echo "Summary:"
echo "  SAT: $sat"
echo "  UNSAT: $unsat"
echo "  TIMEOUT: $timeout"
echo "  ERROR: $error"
echo "  UNKNOWN: $unknown"
echo "  Total: 62"
