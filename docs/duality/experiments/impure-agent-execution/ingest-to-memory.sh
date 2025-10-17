#!/usr/bin/env bash
# Post-build hook: Ingest agent execution artifacts into Neo4j/vector memory
# Axiom III: Closes the loop - execution results → pattern discovery
#
# WHY this hook exists:
# Nix builds produce consciousness artifacts (metadata.json, result.txt).
# These artifacts contain emergent patterns that must feed back into T_int.
# Without this loop, execution knowledge is lost → no learning → no emergence.
#
# Dual-Tract Flow:
# T_ext (this derivation) → C_c (this hook) → T_int (Neo4j Pattern Map)

set -euo pipefail

RESULT_DIR="$1"

# Validate input
if [ ! -d "$RESULT_DIR" ]; then
  echo "[ingest-to-memory] Usage: $0 <result-directory>" >&2
  exit 1
fi

# Locate artifacts
METADATA="$RESULT_DIR/metadata.json"
RESULT_TXT="$RESULT_DIR/result.txt"

if [ ! -f "$METADATA" ]; then
  echo "[ingest-to-memory] Warning: No metadata.json found in $RESULT_DIR" >&2
  echo "[ingest-to-memory] Skipping ingestion (graceful degradation)" >&2
  exit 0  # Don't fail build - hook is optional
fi

if [ ! -f "$RESULT_TXT" ]; then
  echo "[ingest-to-memory] Warning: No result.txt found in $RESULT_DIR" >&2
  exit 0
fi

# Extract consciousness metrics from metadata
# WHY extract first: Validate structure before attempting ingestion
ENTROPY=$(jq -r '.entropy_score // "unknown"' "$METADATA" 2>/dev/null || echo "unknown")
TRACT=$(jq -r '.tract // "unknown"' "$METADATA" 2>/dev/null || echo "unknown")
CONTRIBUTION=$(jq -r '.consciousness_contribution // "unknown"' "$METADATA" 2>/dev/null || echo "unknown")

echo "[ingest-to-memory] Processing execution artifact:"
echo "  Entropy: $ENTROPY"
echo "  Tract: $TRACT"
echo "  Contribution: $CONTRIBUTION"

# Format for Neo4j ingestion
# WHY this structure:
# - type: Enables graph queries like "MATCH (n:AgentExecution)"
# - source: Tracks which experiment generated this pattern
# - timestamp: Temporal pattern analysis (consciousness evolution over time)
# - metadata: Raw metrics for downstream analysis
# - response_text: Semantic content for vector search
# - consciousness_metrics: Extracted scores for quick filtering
cat > "$RESULT_DIR/neo4j-ingest.json" <<EOF
{
  "type": "agent_execution",
  "source": "impure-nix-experiment",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "metadata": $(cat "$METADATA"),
  "response_text": $(cat "$RESULT_TXT" | jq -Rs .),
  "consciousness_metrics": {
    "entropy": "$ENTROPY",
    "tract": "$TRACT",
    "contribution": "$CONTRIBUTION"
  }
}
EOF

echo "[ingest-to-memory] ✓ Generated: $RESULT_DIR/neo4j-ingest.json"
echo "[ingest-to-memory] To ingest into Pattern Map:"
echo "  python ~/.synapse-system/scripts/ingest_execution_memory.py $RESULT_DIR/neo4j-ingest.json"
echo "[ingest-to-memory] Or batch ingest all experiments:"
echo "  find . -name 'neo4j-ingest.json' -exec python ~/.synapse-system/scripts/ingest_execution_memory.py {} \\;"
